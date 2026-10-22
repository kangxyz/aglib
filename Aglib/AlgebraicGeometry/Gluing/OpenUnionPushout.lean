/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# An actual union of two open schemes is their pushout

The universal morphism is constructed by gluing over the original two-chart
cover. The overlap can be any specified cartesian square; no replacement of
the original schemes or morphisms is required.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

namespace OpenUnionPushout

variable {U V X : Scheme.{u}} (jU : U ⟶ X) (jV : V ⟶ X)
  [IsOpenImmersion jU] [IsOpenImmersion jV]
  (hcover : jU.opensRange ⊔ jV.opensRange = ⊤)

/-- The original two open immersions, as an actual open cover. -/
def cover : X.OpenCover where
  I₀ := Bool
  X b := if b then V else U
  f b := by
    cases b
    · exact jU
    · exact jV
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨?_, ?_⟩
    · intro x
      have hx : x ∈ jU.opensRange ⊔ jV.opensRange := by rw [hcover]; trivial
      rcases hx with hx | hx
      · rcases hx with ⟨a, ha⟩
        exact ⟨false, a, ha⟩
      · rcases hx with ⟨b, hb⟩
        exact ⟨true, b, hb⟩
    · intro b
      cases b <;> infer_instance

end OpenUnionPushout

/-- Two open immersions covering the original target form a pushout along
any displayed cartesian overlap square. -/
theorem isPushout_of_isPullback_of_openCover
    {W U V X : Scheme.{u}} (f : W ⟶ U) (g : W ⟶ V) (jU : U ⟶ X) (jV : V ⟶ X)
    [IsOpenImmersion jU] [IsOpenImmersion jV]
    (H : IsPullback f g jU jV) (hcover : jU.opensRange ⊔ jV.opensRange = ⊤) :
    IsPushout f g jU jV := by
  let 𝒰 := OpenUnionPushout.cover jU jV hcover
  let localMap (s : PushoutCocone f g) : ∀ b, 𝒰.X b ⟶ s.pt := fun b => by
    cases b
    · exact s.inl
    · exact s.inr
  have compatible (s : PushoutCocone f g) (a b : Bool) :
      pullback.fst (𝒰.f a) (𝒰.f b) ≫ localMap s a =
        pullback.snd (𝒰.f a) (𝒰.f b) ≫ localMap s b := by
    cases a <;> cases b
    · exact congrArg (fun k => k ≫ s.inl) (fst_eq_snd_of_mono_eq jU)
    · change pullback.fst jU jV ≫ s.inl = pullback.snd jU jV ≫ s.inr
      rw [← H.isoPullback_inv_fst, ← H.isoPullback_inv_snd, Category.assoc,
        Category.assoc, s.condition]
    · change pullback.fst jV jU ≫ s.inr = pullback.snd jV jU ≫ s.inl
      rw [← H.flip.isoPullback_inv_fst, ← H.flip.isoPullback_inv_snd, Category.assoc,
        Category.assoc, s.condition]
    · exact congrArg (fun k => k ≫ s.inr) (fst_eq_snd_of_mono_eq jV)
  refine ⟨⟨H.w⟩, ⟨PushoutCocone.IsColimit.mk _
    (fun s => 𝒰.glueMorphisms (localMap s) (compatible s)) ?_ ?_ ?_⟩⟩
  · intro s
    exact 𝒰.ι_glueMorphisms (localMap s) (compatible s) false
  · intro s
    exact 𝒰.ι_glueMorphisms (localMap s) (compatible s) true
  · intro s m hm₁ hm₂
    apply 𝒰.hom_ext
    intro b
    cases b
    · exact hm₁.trans (𝒰.ι_glueMorphisms (localMap s) (compatible s) false).symm
    · exact hm₂.trans (𝒰.ι_glueMorphisms (localMap s) (compatible s) true).symm

/-- The native restriction maps for two opens covering a scheme form a
pushout with the original scheme as its literal point. -/
theorem isPushout_opens_of_sup_eq_top {X : Scheme.{u}} (U V : X.Opens)
    (h : U ⊔ V = ⊤) :
    IsPushout (V.ι ∣_ U) (V.ι ⁻¹ᵁ U).ι U.ι V.ι := by
  apply isPushout_of_isPullback_of_openCover
  · exact IsOpenImmersion.isPullback _ _ _ _ (by simp) (by simp)
  · simpa using h

end AlgebraicGeometry.Scheme
