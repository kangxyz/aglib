/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# The original image-factor graph over a protected open

The graph of the native map to the schematic image retains the original
source map. If the original range is closed over a protected base open,
its graph is closed over that same open by continuous inverse image. No
quasi-compactness, immersion, or reducedness premise is needed for this transfer.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

variable {T A X : Scheme.{u}} (γ : T ⟶ A) (p : A ⟶ X)

/-- The literal graph of the native image factor, over the original source map. -/
def imageSectionGraph : T ⟶ pullback (𝟙 X) (γ.imageι ≫ p) :=
  pullback.lift (γ ≫ p) γ.toImage (by simp)

@[reassoc (attr := simp)]
lemma imageSectionGraph_fst :
    imageSectionGraph γ p ≫ pullback.fst (𝟙 X) (γ.imageι ≫ p) = γ ≫ p :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma imageSectionGraph_snd :
    imageSectionGraph γ p ≫ pullback.snd (𝟙 X) (γ.imageι ≫ p) = γ.toImage :=
  pullback.lift_snd _ _ _

/-- The exact graph range is the inverse image of the original range under
its canonical injective map back to the original ambient scheme. -/
lemma range_imageSectionGraph :
    Set.range (imageSectionGraph γ p) =
      (pullback.snd (𝟙 X) (γ.imageι ≫ p) ≫ γ.imageι) ⁻¹' Set.range γ := by
  let k := pullback.snd (𝟙 X) (γ.imageι ≫ p) ≫ γ.imageι
  have hk : Function.Injective k :=
    γ.imageι.isClosedEmbedding.injective.comp
      (pullback.snd (𝟙 X) (γ.imageι ≫ p)).isOpenEmbedding.injective
  have hfac : imageSectionGraph γ p ≫ k = γ := by
    simp only [k, imageSectionGraph_snd_assoc, Hom.toImage_imageι]
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, (congrArg (fun t => t y) hfac).symm⟩
  · rintro ⟨y, hy⟩
    refine ⟨y, hk ?_⟩
    change (imageSectionGraph γ p ≫ k) y = k x
    rw [hfac]
    exact hy

/-- Closedness over the protected base open for the graph of the exact original
map to the schematic image. This transfer requires no density assumptions. -/
lemma isClosed_imageSectionGraph_over
    (V : X.Opens) (hclosed : IsClosed ((p ⁻¹ᵁ V).ι ⁻¹' Set.range γ)) :
    IsClosed ((pullback.fst (𝟙 X) (γ.imageι ≫ p) ⁻¹ᵁ V).ι ⁻¹'
      Set.range (imageSectionGraph γ p)) := by
  let B := pullback.fst (𝟙 X) (γ.imageι ≫ p) ⁻¹ᵁ V
  let k := pullback.snd (𝟙 X) (γ.imageι ≫ p) ≫ γ.imageι
  have hkp : k ≫ p = pullback.fst (𝟙 X) (γ.imageι ≫ p) := by
    simpa only [k, Category.assoc, Category.comp_id] using
      (pullback.condition (f := 𝟙 X) (g := γ.imageι ≫ p)).symm
  let kV : B.toScheme → (p ⁻¹ᵁ V).toScheme := fun x => ⟨k x.val, by
    change (k ≫ p) x.val ∈ V
    rw [hkp]
    exact x.property⟩
  have hkV : Continuous kV :=
    (k.continuous.comp continuous_subtype_val).subtype_mk _
  have heq : B.ι ⁻¹' Set.range (imageSectionGraph γ p) =
      kV ⁻¹' ((p ⁻¹ᵁ V).ι ⁻¹' Set.range γ) := by
    rw [range_imageSectionGraph]
    rfl
  change IsClosed (B.ι ⁻¹' Set.range (imageSectionGraph γ p))
  rw [heq]
  exact hclosed.preimage hkV

end AlgebraicGeometry.Scheme.QuasiDomination
