/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Kummer.IntegralModel
public import Mathlib.Algebra.Group.Irreducible.Lemmas

/-! # Whole transverse points of the original root algebra

The image of the actual root already lies in the target ring. An irreducible
image of the original parameter therefore forces exponent one directly,
without selecting a fraction field or assuming integral closedness.
-/

@[expose] public noncomputable section

open Polynomial

namespace Algebra.Kummer

universe u v

variable {A : Type u} [CommRing A] {D : Type v} [CommRing D] [Algebra A D]

/-- A whole original root-algebra point with irreducible parameter image forces
exponent one; positivity and invertibility are conclusions, not premises. -/
theorem exponent_eq_one_of_transversePoint (n : ℕ) (f : A)
    (hf : Irreducible (algebraMap A D f)) (t : RootAlgebra n f →ₐ[A] D) : n = 1 := by
  by_contra hne
  apply not_irreducible_pow hne (x := t (AdjoinRoot.root (rootPolynomial n f)))
  rw [← map_pow, root_pow, t.commutes]
  exact hf

/-- The same original root algebra is etale after the exponent-one conclusion. -/
theorem etale_of_transversePoint (n : ℕ) (f : A)
    (hf : Irreducible (algebraMap A D f)) (t : RootAlgebra n f →ₐ[A] D) :
    Algebra.Etale A (RootAlgebra n f) := by
  have hn := exponent_eq_one_of_transversePoint n f hf t
  subst n
  apply etale_adjoinRoot_of_isUnit_derivative _ (monic_X_pow_sub_C f (by decide : 1 ≠ 0))
  simp only [pow_one, derivative_sub, derivative_X, derivative_C,
    sub_zero, map_one, isUnit_one]

end Algebra.Kummer
