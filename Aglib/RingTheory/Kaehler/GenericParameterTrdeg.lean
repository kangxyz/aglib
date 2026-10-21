/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kaehler.GenericParameter
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.SetTheory.Cardinal.Arithmetic

/-! # Transcendence degree under finite generic parameter extension

The parameter fields and their action are the actual canonical fraction fields.
Only the number of parameters must be finite: the original extension can have
infinite transcendence degree. Cancellation uses finiteness of the common
parameter summand, not finiteness of the differential module.
-/

@[expose] public noncomputable section

open Cardinal

universe u v w

namespace GenericParameterField

attribute [local instance] MvPolynomial.algebraMvPolynomial fractionAlgebra

private theorem fractionPolynomial_trdeg (k : Type u) [Field k] (ι : Type w) :
    Algebra.trdeg k (FractionRing (MvPolynomial ι k)) = Cardinal.lift.{u} (#ι) := by
  let : Algebra.IsAlgebraic (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors (MvPolynomial ι k))
  have h := trdeg_add_eq k (MvPolynomial ι k) (A := FractionRing (MvPolynomial ι k))
  have hzero : Algebra.trdeg (MvPolynomial ι k) (FractionRing (MvPolynomial ι k)) = 0 :=
    trdeg_eq_zero
  rw [hzero, add_zero, MvPolynomial.trdeg_of_isDomain] at h
  exact h.symm

/-- Adjoining the same finite generic parameters to both fields preserves
transcendence degree, with the canonical field action and universe lift. -/
theorem trdeg_fractionAlgebra (k : Type u) (K : Type v) [Field k] [Field K]
    [Algebra k K] (ι : Type w) [Finite ι] :
    Algebra.trdeg (FractionRing (MvPolynomial ι k)) (FractionRing (MvPolynomial ι K)) =
      Cardinal.lift.{w} (Algebra.trdeg k K) := by
  let F := FractionRing (MvPolynomial ι k)
  let L := FractionRing (MvPolynomial ι K)
  have h₁ := congrArg (Cardinal.lift.{u}) (lift_trdeg_add_eq k K L)
  have h₂ := lift_trdeg_add_eq k F L
  have hK : Algebra.trdeg K L = Cardinal.lift.{v} (#ι) := fractionPolynomial_trdeg K ι
  have hk : Algebra.trdeg k F = Cardinal.lift.{u} (#ι) := fractionPolynomial_trdeg k ι
  have h₁' : Cardinal.lift.{max u v w} (Algebra.trdeg k K) +
      Cardinal.lift.{max u v w} (#ι) = Cardinal.lift.{max u v w} (Algebra.trdeg k L) := by
    simpa only [Cardinal.lift_add, hK, Cardinal.lift_lift, ← Cardinal.lift_umax] using h₁
  have h₂' : Cardinal.lift.{max u v w} (#ι) +
      Cardinal.lift.{max u v w} (Algebra.trdeg F L) =
      Cardinal.lift.{max u v w} (Algebra.trdeg k L) := by
    simpa only [hk, Cardinal.lift_lift, ← Cardinal.lift_umax] using h₂
  have he : Cardinal.lift.{max u v w} (Algebra.trdeg F L) =
      Cardinal.lift.{max u v w} (Algebra.trdeg k K) := by
    apply Cardinal.eq_of_add_eq_add_left (h₂'.trans ?_)
      (Cardinal.lift_lt_aleph0.mpr Cardinal.mk_lt_aleph0)
    exact h₁'.symm.trans (add_comm _ _)
  apply Cardinal.lift_inj.{max v w, u}.mp
  simpa only [Cardinal.lift_lift, ← Cardinal.lift_umax] using he

end GenericParameterField
