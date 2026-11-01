/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.IrreduciblePower
public import Aglib.RingTheory.Kummer.IntegralModel

/-! # Transverse fraction-field sections of actual parameter-root charts

If the parameter maps to an irreducible element of an integrally closed ring,
a section of the given root chart over its fraction ring forces exponent one.
The same original chart is then etale. This is the local algebra obstruction in
Stacks 0EYI, not a construction of the tame normal-form charts of 0EYH.
-/

@[expose] public section

namespace Algebra.Kummer

open Polynomial

universe u v w

variable {A : Type u} [CommRing A]
  {R : Type v} [CommRing R] [IsIntegrallyClosed R] [Algebra A R]
  {K : Type w} [CommRing K] [Algebra R K] [IsFractionRing R K]
  [Algebra A K] [IsScalarTower A R K]

omit [IsIntegrallyClosed R] [IsFractionRing R K] in
/-- A genuine fraction-ring section of the original parameter-root chart
retains its actual parameter equation through the given algebra tower. -/
theorem transverseSection_root_pow (n : ℕ) (f : A)
    (s : RootAlgebra n f →ₐ[A] K) :
    s (AdjoinRoot.root (rootPolynomial n f)) ^ n =
      algebraMap R K (algebraMap A R f) := by
  rw [← map_pow, root_pow, s.commutes]
  exact IsScalarTower.algebraMap_apply A R K f

/-- An actual generic section meeting the parameter transversely forces the
original chart exponent to be one, without a positivity or invertibility premise. -/
theorem exponent_eq_one_of_transverseSection (n : ℕ) (f : A)
    (hf : Irreducible (algebraMap A R f)) (s : RootAlgebra n f →ₐ[A] K) : n = 1 :=
  IsIntegrallyClosed.eq_one_of_pow_eq_irreducible hf
    (transverseSection_root_pow (R := R) n f s)

/-- The unchanged parameter-root chart is etale when it has an actual generic
section transverse to its parameter. This does not assume or construct tame charts. -/
theorem etale_of_transverseSection (n : ℕ) (f : A)
    (hf : Irreducible (algebraMap A R f)) (s : RootAlgebra n f →ₐ[A] K) :
    Algebra.Etale A (RootAlgebra n f) := by
  have hn := exponent_eq_one_of_transverseSection n f hf s
  subst n
  apply etale_adjoinRoot_of_isUnit_derivative _ (monic_X_pow_sub_C f (by decide : 1 ≠ 0))
  simp only [pow_one, derivative_sub, derivative_X, derivative_C,
    sub_zero, map_one, isUnit_one]

end Algebra.Kummer
