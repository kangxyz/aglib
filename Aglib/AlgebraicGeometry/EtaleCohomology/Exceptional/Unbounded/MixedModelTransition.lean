/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompactificationDiagram
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawTransitionCoherence

/-! # Original refinement transitions with independent middle models

The geometric identity is allowed to carry different native derived models on
its two sides. Composition retains the original refinement-unit maps and proper
image compositors. No same-scheme instance is identified implicitly.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wC wD wE
variable {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

section Mixed
variable {C D : Hom.DenseCompactification f} (a : C ⟶ D)
  [hC : HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ)]
  [hD : HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ)]

/-- The original refinement transition with independently specified models. -/
def moduleUnboundedCompactificationMixedTransition :
    moduleUnboundedCompactificationFunctor f Λ D ⟶ moduleUnboundedCompactificationFunctor f Λ C :=
  CategoryTheory.imageComparison (moduleUnboundedDerivedRefinementComparison a Λ)
      (moduleUnboundedDerivedRefinementDirectImageIso Λ a)

/-- The original mixed-model map is invertible on the full unbounded source
for a torsion coefficient ring. -/
theorem moduleUnboundedCompactificationMixedTransition_isIso
    (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0) :
    IsIso (moduleUnboundedCompactificationMixedTransition Λ a) := by
  have (K : DerivedCategory (ModuleSheaf X Λ)) :
      IsIso ((moduleUnboundedCompactificationMixedTransition Λ a).app K) := by
    let : IsIso ((moduleUnboundedDerivedRefinementComparison a Λ).app K) :=
      moduleUnboundedDerivedRefinementComparison_isIso a Λ N hN hΛ K
    exact CategoryTheory.imageComparison_isIso_app (moduleUnboundedDerivedRefinementComparison a Λ)
      (moduleUnboundedDerivedRefinementDirectImageIso Λ a) K
  exact NatIso.isIso_of_isIso_app _

variable {E : Hom.DenseCompactification f} (b : D ⟶ E)
  [hE : HasDerivedCategory.{wE} (ModuleSheaf E.Xbar Λ)]

/-- Composition remains valid when all three middle models are independent. -/
theorem moduleUnboundedCompactificationMixedTransition_comp :
    moduleUnboundedCompactificationMixedTransition Λ (a ≫ b) =
      moduleUnboundedCompactificationMixedTransition Λ b ≫
        moduleUnboundedCompactificationMixedTransition Λ a := by
  have h := CategoryTheory.imageComparison_comp (moduleUnboundedDerivedRefinementComparison a Λ)
    (moduleUnboundedDerivedRefinementComparison b Λ)
    (moduleUnboundedDerivedRefinementComparison (a ≫ b) Λ)
    (moduleUnboundedDerivedDirectImageCompIso Λ b.hom a.hom)
    (moduleUnboundedDerivedRefinementDirectImageIso Λ a)
    (moduleUnboundedDerivedRefinementDirectImageIso Λ b)
    (moduleUnboundedDerivedRefinementDirectImageIso Λ (a ≫ b))
    (moduleUnboundedDerivedRefinementComparison_comp Λ a b)
    (moduleUnboundedDerivedRefinementDirectImageIso_comp Λ a b)
  exact h
end Mixed

end AlgebraicGeometry.Scheme.EtaleCohomology
