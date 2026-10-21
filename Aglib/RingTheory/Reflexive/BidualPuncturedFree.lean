/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Reflexive.EvaluationLocalization
public import Aglib.RingTheory.Support.FiniteDefect
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Bidual evaluation for a punctured-free module

Punctured freeness gives finite-length defects of the original bidual evaluation
and punctured freeness of its target. No global injectivity of evaluation or
reflexivity of the original module is required.
-/

@[expose] public section

noncomputable section

namespace Module

variable {R : Type*} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {M : Type*} [AddCommGroup M] [Module R M] [Module.Finite R M]
    (hfree : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M))

include hfree

/-- The actual evaluation is bijective after localization on the punctured spectrum. -/
theorem localized_eval_bijective_of_free_punctured
    (p : PrimeSpectrum R) (hp : p.asIdeal ≠ IsLocalRing.maximalIdeal R) :
    Function.Bijective (LocalizedModule.map p.asIdeal.primeCompl (Dual.eval R M)) := by
  have := hfree p hp
  have := Module.finitePresentation_of_finite R M
  have := Module.finitePresentation_of_finite R (Dual R M)
  exact Dual.localized_eval_bijective p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
    (LocalizedModule.mkLinearMap p.asIdeal.primeCompl M)

/-- Both actual bidual-evaluation errors have finite length. -/
theorem isFiniteLength_eval_defects_of_free_punctured :
    IsFiniteLength R (Dual.eval R M).ker ∧
      IsFiniteLength R (Dual R (Dual R M) ⧸ (Dual.eval R M).range) := by
  exact ⟨(Dual.eval R M).isFiniteLength_ker_of_injective_punctured
      (fun p hp ↦ (localized_eval_bijective_of_free_punctured hfree p hp).1),
    (Dual.eval R M).isFiniteLength_coker_of_surjective_punctured
      (fun p hp ↦ (localized_eval_bijective_of_free_punctured hfree p hp).2)⟩

/-- The bidual is free at each punctured prime, using the original localized evaluation. -/
theorem free_punctured_doubleDual_of_free_punctured
    (p : PrimeSpectrum R) (hp : p.asIdeal ≠ IsLocalRing.maximalIdeal R) :
    Module.Free (Localization.AtPrime p.asIdeal)
      (LocalizedModule p.asIdeal.primeCompl (Dual R (Dual R M))) := by
  have := hfree p hp
  let e := LinearEquiv.ofBijective
    (LocalizedModule.map p.asIdeal.primeCompl (Dual.eval R M))
    (localized_eval_bijective_of_free_punctured hfree p hp)
  exact Module.Free.of_equiv e

end Module
