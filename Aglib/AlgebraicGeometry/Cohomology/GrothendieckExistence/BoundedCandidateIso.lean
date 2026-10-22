/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.BoundedCandidateIsoAssembly
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.BoundedCandidateIsoOnAffineChart
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.CandidateIsoComparison

/-! # Actual global isomorphisms between genuine bounded candidates

Local original affine isomorphisms glue because their maps to the same original
ambient agree. Monicity forces all overlap equations. No completion-faithfulness,
ambient quasicoherence, separatedness, or hypothetical gluing input is used.
-/

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

/-- The actual bounded candidate isomorphism retains the original algebraic
map and every original specified formal-stage map. -/
def boundedCandidateIsoComparison :
    CandidateIsoComparison a₁ β₁ a₂ β₂ := by
  letI : Mono (boundedCandidateLift α a₂ β₂ h₂) :=
    boundedCandidateLift_mono α a₂ β₂ h₂ t₂ hk₂ hc₂
  let U := X.affineOpenCover
  letI (i : U.I₀) : IsNoetherianRing (U.X i) :=
    isLocallyNoetherian_Spec.mp (isLocallyNoetherian_of_isOpenImmersion (U.f i))
  refine boundedCandidateIsoOfLocalComparisons
    (X := X) (K := K) (F := F) (H := H) (G₁ := G₁) (G₂ := G₂)
    (fun i => Spec (U.X i)) U.f U.openCover.exists_eq
    α a₁ β₁ h₁ a₂ β₂ h₂ ?_
  intro i
  exact boundedCandidateIsoOnAffineChart
    (X := X) (K := K) (F := F) (H := H) (G₁ := G₁) (G₂ := G₂)
    (B := U.X i) α a₁ β₁ h₁ t₁ hk₁ hc₁ a₂ β₂ h₂ t₂ hk₂ hc₂ (U.f i)

end AlgebraicGeometry.Scheme.Modules.Coherent
