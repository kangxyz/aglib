/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Reflexive.QuotientEndomorphism
public import Aglib.RingTheory.RegularLocalRing.FiniteLengthDualComparison

/-! Canonical quotient-endomorphism action and the actual finite-defect bidual extension. -/

@[expose] public section

universe u

example {R : Type*} [CommRing R] (a : R) (M : Type*) [AddCommGroup M] [Module R M]
    (f : Module.End R M) (x : M) :
    QuotSMulTop.quotientEndomorphismDoubleDual a M (Submodule.Quotient.mk f)
      (Module.Dual.eval (R ⧸ Ideal.span {a}) (QuotSMulTop a M) (Submodule.Quotient.mk x)) =
    Module.Dual.eval (R ⧸ Ideal.span {a}) (QuotSMulTop a M)
      (Submodule.Quotient.mk (f x)) := rfl

example (R : Type u) [CommRing R] [IsRegularLocalRing R]
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hker : IsFiniteLength R f.ker)
    (hcoker : IsFiniteLength R (N ⧸ f.range))
    (d : ℕ) (hd : ringKrullDim R = (d : ℕ)) (h2 : 2 ≤ d) (x : M) :
    (LinearEquiv.ofBijective f.dualMap.dualMap
      (IsRegularLocalRing.bijective_doubleDualMap_of_isFiniteLength R f hker hcoker d hd h2))
        (Module.Dual.eval R M x) = Module.Dual.eval R N (f x) := rfl
