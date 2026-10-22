/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.OpenBoundedCandidate
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineBoundedCandidateIso
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.CandidateIsoComparison

/-! # Whole original candidate comparisons on an actual affine chart -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {K : X.IdealSheafData} {F : AdicSystem X K} {H G₁ G₂ : X.CoherentSheaf}
  (α : F ⟶ (completionFunctor X K).obj H)
  (a₁ : G₁ ⟶ H) (β₁ : (completionFunctor X K).obj G₁ ≅ F)
  (h₁ : β₁.hom ≫ α = (completionFunctor X K).map a₁)
  (t₁ : ℕ) (hk₁ : killedByIdealSheaf (K ^ t₁) (kernel a₁.hom))
  (hc₁ : killedByIdealSheaf (K ^ t₁) (cokernel a₁.hom))
  (a₂ : G₂ ⟶ H) (β₂ : (completionFunctor X K).obj G₂ ≅ F)
  (h₂ : β₂.hom ≫ α = (completionFunctor X K).map a₂)
  (t₂ : ℕ) (hk₂ : killedByIdealSheaf (K ^ t₂) (kernel a₂.hom))
  (hc₂ : killedByIdealSheaf (K ^ t₂) (cokernel a₂.hom))

/-- The actual affine comparison retains its original pulled target and units. -/
def boundedCandidateIsoOnAffineChart {B : CommRingCat.{u}} [IsNoetherianRing B]
    (p : Spec B ⟶ X) [IsOpenImmersion p] :
    CandidateIsoComparison ((coherentPullback p).map a₁)
      (openReconstructionCandidateIso p β₁) ((coherentPullback p).map a₂)
      (openReconstructionCandidateIso p β₂) :=
  affineBoundedCandidateIsoComparison
    (openReconstructionComparison p α)
    ((coherentPullback p).map a₁) (openReconstructionCandidateIso p β₁)
    (openReconstructionCandidateIso_square p α a₁ β₁ h₁) t₁
    (openReconstructionCandidate_bounds p a₁ t₁ hk₁ hc₁).1
    (openReconstructionCandidate_bounds p a₁ t₁ hk₁ hc₁).2
    ((coherentPullback p).map a₂) (openReconstructionCandidateIso p β₂)
    (openReconstructionCandidateIso_square p α a₂ β₂ h₂) t₂
    (openReconstructionCandidate_bounds p a₂ t₂ hk₂ hc₂).1
    (openReconstructionCandidate_bounds p a₂ t₂ hk₂ hc₂).2

end AlgebraicGeometry.Scheme.Modules.Coherent
