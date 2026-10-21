/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.TensorProduct.DualEvaluation
public import Aglib.RingTheory.Support.FiniteDefect

/-!
# Finite-length defects of tensor-dual evaluation

Punctured-spectrum freeness makes the actual evaluation locally bijective.
Its kernel and cokernel are consequently supported at the closed point.
-/

@[expose] public section

open TensorProduct

namespace Module

variable {R M : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- Punctured freeness gives finite length for the actual evaluation kernel. -/
theorem isFiniteLength_ker_tensorDualEvaluation_of_free_punctured
    (hfree : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M)) :
    IsFiniteLength R (tensorDualEvaluation R M).ker := by
  have := Module.finitePresentation_of_finite R M
  apply LinearMap.isFiniteLength_ker_of_injective_punctured
  intro p hp
  have := hfree p hp
  exact (tensorDualEvaluation_localized_bijective p.asIdeal.primeCompl).1

/-- Punctured freeness gives finite length for the actual evaluation cokernel. -/
theorem isFiniteLength_coker_tensorDualEvaluation_of_free_punctured
    (hfree : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M)) :
    IsFiniteLength R (Module.End R M ⧸ (tensorDualEvaluation R M).range) := by
  have := Module.finitePresentation_of_finite R M
  apply LinearMap.isFiniteLength_coker_of_surjective_punctured
  intro p hp
  have := hfree p hp
  exact (tensorDualEvaluation_localized_bijective p.asIdeal.primeCompl).2

end Module
