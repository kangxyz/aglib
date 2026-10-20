/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.AlgebraicSimplex.Basic
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# Units of actual algebraic simplex coordinate rings
-/

@[expose] public section


noncomputable section
namespace AlgebraicGeometry.AlgebraicSimplex
universe u
variable (K : Type u) [Field K]

/-- The actual one-simplex coordinate ring is a polynomial PID. -/
instance coordinateRingOne_isPrincipalIdealRing :
    IsPrincipalIdealRing (AlgebraicSimplex.CoordinateRing K 1) := by
  let e := (AlgebraicSimplex.polynomialEquiv K 1).trans (MvPolynomial.uniqueAlgEquiv K (Fin 1))
  exact IsPrincipalIdealRing.of_surjective e.symm.toRingHom e.symm.surjective

/-- Every invertible regular function on an affine simplex over a field is constant. -/
theorem unit_constant (n : ℕ) (a : (AlgebraicSimplex.CoordinateRing K n)ˣ) :
    ∃ c : K, (a : AlgebraicSimplex.CoordinateRing K n) =
      algebraMap K (AlgebraicSimplex.CoordinateRing K n) c := by
  let e := AlgebraicSimplex.polynomialEquiv K n
  have h : IsUnit (e (a : AlgebraicSimplex.CoordinateRing K n)) :=
    a.isUnit.map e.toRingHom
  obtain ⟨c, _, hc⟩ := MvPolynomial.isUnit_iff_eq_C_of_isReduced.mp h
  refine ⟨c, e.injective ?_⟩
  rw [e.commutes]
  exact hc

/-- Any two K-algebra specializations have equal values on simplex units. -/
theorem unit_specialization (n : ℕ)
    (f g : AlgebraicSimplex.CoordinateRing K n →ₐ[K] K)
    (a : (AlgebraicSimplex.CoordinateRing K n)ˣ) :
    Units.map f.toRingHom.toMonoidHom a = Units.map g.toRingHom.toMonoidHom a := by
  obtain ⟨c, hc⟩ := unit_constant K n a
  apply Units.ext
  change f (a : AlgebraicSimplex.CoordinateRing K n) = g (a : AlgebraicSimplex.CoordinateRing K n)
  rw [hc, f.commutes, g.commutes]

end AlgebraicGeometry.AlgebraicSimplex

namespace AlgebraicGeometry.AlgebraicSimplex
universe u
variable (K : Type u) [CommRing K]

/-- A base-ring unit viewed as a constant unit on the genuine algebraic simplex. -/
def constantUnit (a : Kˣ) (n : ℕ) : (AlgebraicSimplex.CoordinateRing K n)ˣ :=
  Units.map (algebraMap K (AlgebraicSimplex.CoordinateRing K n)).toMonoidHom a

/-- Every simplex pullback fixes constant units. -/
@[simp] theorem pullback_constantUnit (a : Kˣ) {m n : ℕ}
    (f : Fin (m + 1) → Fin (n + 1)) :
    Units.map (AlgebraicSimplex.pullback K f).toRingHom.toMonoidHom (constantUnit K a n) =
      constantUnit K a m := by
  apply Units.ext
  exact (AlgebraicSimplex.pullback K f).commutes (a : K)

end AlgebraicGeometry.AlgebraicSimplex

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/AlgebraicSimplex/Units.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 7ba9dc74421a23f962b2aea5288d0abfb7f137e40355cc0cfd886a58921bafc9.
Native names and imports replace the source wrappers; stated conditions and maps are retained. -/
