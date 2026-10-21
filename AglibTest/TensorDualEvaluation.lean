/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.TensorProduct.DualEvaluationFiniteLength

/-! Independent carrier universes and the original rank-one evaluation map. -/

@[expose] public section

open TensorProduct

universe u v

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

example (m x : M) (f : Module.Dual R M) :
    Module.tensorDualEvaluation R M (m ⊗ₜ[R] f) x = f x • m := rfl

example [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M]
    (hf : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Module.Free (Localization.AtPrime p.asIdeal) (LocalizedModule p.asIdeal.primeCompl M)) :
    IsFiniteLength R (Module.tensorDualEvaluation R M).ker ∧
      IsFiniteLength R (Module.End R M ⧸ (Module.tensorDualEvaluation R M).range) :=
  ⟨Module.isFiniteLength_ker_tensorDualEvaluation_of_free_punctured hf,
    Module.isFiniteLength_coker_tensorDualEvaluation_of_free_punctured hf⟩

universe w

variable {N : Type w} [AddCommGroup N] [Module R N]

example [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R M] (f : M →ₗ[R] N)
    (hf : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Function.Injective (LocalizedModule.map p.asIdeal.primeCompl f)) :
    IsFiniteLength R f.ker :=
  f.isFiniteLength_ker_of_injective_punctured hf

example [IsNoetherianRing R] [IsLocalRing R] [Module.Finite R N] (f : M →ₗ[R] N)
    (hf : ∀ p : PrimeSpectrum R, p.asIdeal ≠ IsLocalRing.maximalIdeal R →
      Function.Surjective (LocalizedModule.map p.asIdeal.primeCompl f)) :
    IsFiniteLength R (N ⧸ f.range) :=
  f.isFiniteLength_coker_of_surjective_punctured hf
