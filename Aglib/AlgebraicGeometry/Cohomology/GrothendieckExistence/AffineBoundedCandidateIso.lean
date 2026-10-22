/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineBoundedCandidate
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineIsoRecovery

/-! # Original isomorphisms between affine bounded reconstruction candidates

Both candidates retain their original algebraic maps and specified formal
comparisons. The recovered isomorphism commutes with both original projections.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {B : CommRingCat.{u}} [IsNoetherianRing B]
  {K : (Spec B).IdealSheafData} {F : AdicSystem (Spec B) K}
  {H G₁ G₂ : (Spec B).CoherentSheaf}
  (α : F ⟶ (completionFunctor (Spec B) K).obj H)
  (a₁ : G₁ ⟶ H) (β₁ : (completionFunctor (Spec B) K).obj G₁ ≅ F)
  (h₁ : β₁.hom ≫ α = (completionFunctor (Spec B) K).map a₁)
  (t₁ : ℕ) (hk₁ : killedByIdealSheaf (K ^ t₁) (kernel a₁.hom))
  (hc₁ : killedByIdealSheaf (K ^ t₁) (cokernel a₁.hom))
  (a₂ : G₂ ⟶ H) (β₂ : (completionFunctor (Spec B) K).obj G₂ ≅ F)
  (h₂ : β₂.hom ≫ α = (completionFunctor (Spec B) K).map a₂)
  (t₂ : ℕ) (hk₂ : killedByIdealSheaf (K ^ t₂) (kernel a₂.hom))
  (hc₂ : killedByIdealSheaf (K ^ t₂) (cokernel a₂.hom))

/-- The whole native isomorphism comparison retains both original projections. -/
def affineBoundedCandidateIsoComparison :
    {e : G₁ ≅ G₂ // e.hom ≫ a₂ = a₁ ∧ ∀ n : ℕ,
      e.hom.hom ≫ (idealSheafQuotientUnit (Spec B) (K ^ n)).app G₂.obj ≫
        β₂.hom.hom.app (op n) =
      (idealSheafQuotientUnit (Spec B) (K ^ n)).app G₁.obj ≫
        β₁.hom.hom.app (op n)} := by
  let e₁ := affineCandidatePullbackEquiv α a₁ β₁ h₁ t₁ hk₁ hc₁
  let e₂ := affineCandidatePullbackEquiv α a₂ β₂ h₂ t₂ hk₂ hc₂
  let e := e₁.trans e₂.symm
  refine ⟨affineIsoOfSections G₁ G₂ e, ?_, ?_⟩
  · apply ObjectProperty.hom_ext
    apply affineHom_ext G₁ H
    simp only [ObjectProperty.FullSubcategory.comp_hom, Functor.map_comp,
      affineIsoOfSections_map]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hp : e₂ (e x) = e₁ x := e₂.apply_symm_apply (e₁ x)
    have ht := congrArg (fun z => z.val.2) hp
    change (affineCandidatePullbackEquiv α a₂ β₂ h₂ t₂ hk₂ hc₂ (e x)).val.2 =
      (affineCandidatePullbackEquiv α a₁ β₁ h₁ t₁ hk₁ hc₁ x).val.2 at ht
    rw [affineCandidatePullbackEquiv_toTarget, affineCandidatePullbackEquiv_toTarget] at ht
    exact ht
  · intro n
    apply affineHom_ext G₁ (F.affineCoefficient (op n))
    simp only [Functor.map_comp, affineIsoOfSections_map]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hp : e₂ (e x) = e₁ x := e₂.apply_symm_apply (e₁ x)
    have ht := congrArg (fun z => z.val.1.val (op n)) hp
    change (affineCandidatePullbackEquiv α a₂ β₂ h₂ t₂ hk₂ hc₂
      (e x)).val.1.val (op n) =
      (affineCandidatePullbackEquiv α a₁ β₁ h₁ t₁ hk₁ hc₁ x).val.1.val (op n) at ht
    rw [affineCandidatePullbackEquiv_toStage, affineCandidatePullbackEquiv_toStage] at ht
    exact ht

end AlgebraicGeometry.Scheme.Modules.Coherent
