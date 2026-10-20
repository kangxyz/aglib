/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Tactic.FinCases
public import Aglib.AlgebraicGeometry.AlgebraicSimplex.Basic
public import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# The actual zero-simplex coefficient equivalence
-/

@[expose] public section


noncomputable section
set_option autoImplicit false

namespace AlgebraicGeometry.AlgebraicSimplex
universe u
variable (K : Type u) [CommRing K]

/-- The literal zero-simplex quotient is canonically its coefficient ring. -/
def zeroEquiv : CoordinateRing K 0 ≃ₐ[K] K :=
  (polynomialEquiv K 0).trans (MvPolynomial.isEmptyAlgEquiv K (Fin 0))

@[simp] theorem zeroEquiv_algebraMap (x : K) :
    zeroEquiv K (algebraMap K (CoordinateRing K 0) x) = x :=
  (zeroEquiv K).commutes x

@[simp] theorem zeroEquiv_symm_apply (x : K) :
    (zeroEquiv K).symm x = algebraMap K (CoordinateRing K 0) x :=
  (zeroEquiv K).symm.commutes x

@[simp] theorem coordinate_zero_simplex (i : Fin 1) : coordinate K 0 i = 1 := by
  have hi : i = 0 := Subsingleton.elim _ _
  subst i
  have h := sum_coordinate K 0
  change (∑ i : Fin 1, coordinate K 0 i) = 1 at h
  simpa only [Fin.sum_univ_one] using h

@[simp] theorem zeroEquiv_coordinate (i : Fin 1) :
    zeroEquiv K (coordinate K 0 i) = 1 := by
  rw [coordinate_zero_simplex, map_one]

/-- The isomorphism has the actual vertex evaluation as its forward map. -/
theorem zeroEquiv_eq_vertexEvaluation :
    (zeroEquiv K).toAlgHom = vertexEvaluation K 0 0 := by
  apply hom_ext
  intro i
  fin_cases i
  simp

end AlgebraicGeometry.AlgebraicSimplex

namespace AlgebraicGeometry.AlgebraicSimplex
universe u
variable (K : Type u) [Field K]

/-- The field structure preserves the existing quotient-ring operations. -/
abbrev zeroField : Field (CoordinateRing K 0) :=
  Field.ofIsUnitOrEqZero (fun x => by
    classical
    by_cases hx : zeroEquiv K x = 0
    · right
      apply (zeroEquiv K).injective
      simpa using hx
    · left
      have h := (isUnit_iff_ne_zero.mpr hx).map (zeroEquiv K).symm.toRingHom
      change IsUnit ((zeroEquiv K).symm (zeroEquiv K x)) at h
      simpa only [AlgEquiv.symm_apply_apply] using h)

end AlgebraicGeometry.AlgebraicSimplex


/- Migration source: R5Lab/Aglib/AlgebraicGeometry/AlgebraicSimplex/Zero.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 ccf0dbf2b84adb9d523bfb0b18714582cafbe9bc5ed9159674c8ee6eef78a537.
Native names and imports replace the source wrappers; stated conditions and maps are retained. -/
