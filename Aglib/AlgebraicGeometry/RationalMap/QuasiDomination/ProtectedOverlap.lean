/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Exact source identifications on protected overlaps

An equality of ambient open intersections gives a native isomorphism from
the actual intersection subscheme to the original protected open. The forward
map preserves the morphism to the original base. A separate topological lemma
transports density using an actual isomorphism on a larger protected open;
it does not assert schematic density.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.QuasiDomination

variable {X B : Scheme.{u}} (q : B ⟶ X) (U V : X.Opens) (W : B.Opens)
    (hW : W ⊓ q ⁻¹ᵁ V = q ⁻¹ᵁ U)

include hW in
/-- The literal image of the overlap is the full smaller protected preimage. -/
lemma protectedOverlap_image : W.ι ''ᵁ (W.ι ⁻¹ᵁ q ⁻¹ᵁ V) = q ⁻¹ᵁ U := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact hW

/-- The actual overlap subscheme is identified with the original smaller open,
using the inverse-image isomorphism of the actual ambient morphism. -/
def protectedOverlapIso [IsIso (q ∣_ U)] :
    (W.ι ⁻¹ᵁ q ⁻¹ᵁ V).toScheme ≅ U.toScheme :=
  W.ι.isoImage (W.ι ⁻¹ᵁ q ⁻¹ᵁ V) ≪≫
    B.isoOfEq (protectedOverlap_image q U V W hW) ≪≫ asIso (q ∣_ U)

/-- The source identification retains the original base map, not just points. -/
@[reassoc (attr := simp)]
theorem protectedOverlapIso_hom_ι [IsIso (q ∣_ U)] :
    (protectedOverlapIso q U V W hW).hom ≫ U.ι =
      (W.ι ⁻¹ᵁ q ⁻¹ᵁ V).ι ≫ W.ι ≫ q := by
  simp only [protectedOverlapIso, Iso.trans_hom, asIso_hom, Category.assoc,
    morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc, Scheme.Hom.isoImage_hom_ι_assoc]

/-- The literal restriction of a base-changed morphism is unchanged over
the inverse image of any open on which the original morphism is unchanged. -/
theorem pullback_snd_restrict_isIso {X B Z : Scheme.{u}} (β : B ⟶ X)
    (q : Z ⟶ X) (V : X.Opens) [IsIso (β ∣_ V)] :
    IsIso ((pullback.snd β q) ∣_ q ⁻¹ᵁ V) := by
  have hp : (pullback.fst β q) ⁻¹ᵁ β ⁻¹ᵁ V =
      (pullback.snd β q) ⁻¹ᵁ q ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]
  have h := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback β q)
    (US := V) (UT := q ⁻¹ᵁ V) (UX := β ⁻¹ᵁ V) le_rfl le_rfl
    (UY := (pullback.snd β q) ⁻¹ᵁ q ⁻¹ᵁ V) (by rw [hp, inf_idem])
  have hi : IsIso (β.resLE V (β ⁻¹ᵁ V) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]
    infer_instance
  have hi' := MorphismProperty.of_isPullback h hi
  simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using hi'

/-- Topological density pulls back through a morphism that is an isomorphism
on a protected open whose inverse image is dense. This uses no schematic
density assumption and does not turn topological density into one. -/
theorem dense_preimage_of_dense_protected (q : B ⟶ X) (V : X.Opens)
    [IsIso (q ∣_ V)] (hV : Dense ((q ⁻¹ᵁ V : B.Opens) : Set B))
    (U : X.Opens) (hU : Dense (U : Set X)) : Dense ((q ⁻¹ᵁ U : B.Opens) : Set B) := by
  have hr : DenseRange (q ⁻¹ᵁ V).ι := by
    change Dense (Set.range (q ⁻¹ᵁ V).ι)
    rwa [Scheme.Opens.range_ι]
  have : IsOpenImmersion ((q ⁻¹ᵁ V).ι ≫ q) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have hd := hU.preimage ((q ⁻¹ᵁ V).ι ≫ q).isOpenEmbedding.isOpenMap
  exact hr.dense_of_mapsTo (q ⁻¹ᵁ V).ι.continuous hd (fun _ hx ↦ hx)

end AlgebraicGeometry.Scheme.QuasiDomination
