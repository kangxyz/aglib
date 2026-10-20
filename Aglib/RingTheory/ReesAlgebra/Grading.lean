/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.ReesAlgebra
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Algebra.Polynomial.Degree.Support

/-!
# The actual polynomial grading of the native Rees algebra

The carrier is the existing `reesAlgebra I` inside A[t]. Degree n consists of
its actual polynomials supported at n, with their original ideal-power
coefficients. Polynomial coefficients prove the internal direct sum.
Degree zero is identified with the original base ring by constant coefficient,
including the equation for the original scalar map.

All statements hold over arbitrary commutative rings and arbitrary ideals.
No domain, Noetherian, nontriviality or nonzero-generator condition is used.
This supplies the grading/base-ring bridge for the actual blowup construction;
it does not construct the blowup, its saturated affine atlas or universality.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open Polynomial DirectSum
universe u
namespace reesAlgebra
variable {A : Type u} [CommRing A]

/-- The actual homogeneous polynomials of degree n in the existing Rees algebra. -/
def grading (I : Ideal A) (n : ℕ) : Submodule A (reesAlgebra I) where
  carrier := {p | ∀ m : ℕ, m ≠ n → (p : A[X]).coeff m = 0}
  zero_mem' := by intro m hm; simp
  add_mem' := by
    intro p q hp hq m hm
    change ((p : A[X]) + (q : A[X])).coeff m = 0
    simp only [coeff_add, hp m hm, hq m hm, zero_add]
  smul_mem' := by
    intro a p hp m hm
    change (a • (p : A[X])).coeff m = 0
    simp only [coeff_smul, hp m hm, smul_zero]

lemma eq_monomial_coeff {I : Ideal A} {n : ℕ} {p : reesAlgebra I}
    (hp : p ∈ grading I n) : (p : A[X]) = monomial n ((p : A[X]).coeff n) := by
  ext k
  by_cases h : k = n
  · subst k; simp
  · rw [coeff_monomial, ite_eq_right (Ne.symm h)]
    exact hp k h

/-- The original monomial with its actual ideal-power coefficient. -/
def homogeneous (I : Ideal A) (n : ℕ) (a : ↥(I ^ n : Ideal A)) : grading I n :=
  ⟨⟨monomial n a, reesAlgebra.monomial_mem.mpr a.property⟩, by
    intro m hm
    change (monomial n (a : A)).coeff m = 0
    rw [coeff_monomial, ite_eq_right (Ne.symm hm)]⟩

instance (I : Ideal A) : SetLike.GradedMonoid (grading I) where
  one_mem := by
    intro m hm
    change (1 : A[X]).coeff m = 0
    rw [coeff_one]
    exact ite_eq_right hm
  mul_mem := by
    intro i j p q hp hq m hm
    change ((p : A[X]) * (q : A[X])).coeff m = 0
    rw [eq_monomial_coeff hp, eq_monomial_coeff hq,
      monomial_mul_monomial, coeff_monomial, ite_eq_right (Ne.symm hm)]

lemma coeff_coeAddMonoidHom (I : Ideal A)
    (w : ⨁ n : ℕ, grading I n) (n : ℕ) :
    ((DirectSum.coeAddMonoidHom (grading I) w : reesAlgebra I) : A[X]).coeff n =
      (((w n : grading I n) : reesAlgebra I) : A[X]).coeff n := by
  induction w using DirectSum.induction_on with
  | zero => simp
  | of j p =>
      rw [DirectSum.coeAddMonoidHom_of]
      by_cases h : j = n
      · subst j; simp
      · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm h)]
        change ((p : reesAlgebra I) : A[X]).coeff n = 0
        exact p.property n (Ne.symm h)
  | add x y hx hy =>
      simpa only [map_add, AddMemClass.coe_add, coeff_add, DirectSum.add_apply] using
        congrArg₂ (· + ·) hx hy

lemma grading_isInternal (I : Ideal A) : DirectSum.IsInternal (grading I) := by
  classical
  constructor
  · intro x y h
    apply DFinsupp.ext
    intro n
    apply Subtype.ext
    apply Subtype.ext
    have he := congrArg (fun p : reesAlgebra I => (p : A[X]).coeff n) h
    rw [coeff_coeAddMonoidHom, coeff_coeAddMonoidHom] at he
    rw [eq_monomial_coeff (x n).property, eq_monomial_coeff (y n).property]
    exact congrArg (monomial n) he
  · intro p
    let z : ⨁ n : ℕ, grading I n :=
      ∑ n ∈ (p : A[X]).support,
        DirectSum.of _ n (homogeneous I n ⟨(p : A[X]).coeff n, p.property n⟩)
    refine ⟨z, ?_⟩
    apply Subtype.ext
    simp only [z, map_sum, DirectSum.coeAddMonoidHom_of,
      AddSubmonoidClass.coe_finsetSum, homogeneous]
    exact (p : A[X]).as_sum_support.symm

instance (I : Ideal A) : GradedAlgebra (grading I) :=
  (grading_isInternal I).gradedAlgebra

lemma decompose_coeff (I : Ideal A) (p : reesAlgebra I) (n : ℕ) :
    (((DirectSum.decompose (grading I) p n : grading I n) : reesAlgebra I) : A[X]).coeff n =
      (p : A[X]).coeff n := by
  have h := coeff_coeAddMonoidHom I (DirectSum.decompose (grading I) p) n
  have he : DirectSum.coeAddMonoidHom (grading I)
      (DirectSum.decompose (grading I) p) = p :=
    (DirectSum.decompose (grading I)).symm_apply_apply p
  rw [he] at h
  exact h.symm

lemma decompose_val (I : Ideal A) (p : reesAlgebra I) (n : ℕ) :
    (((DirectSum.decompose (grading I) p n : grading I n) : reesAlgebra I) : A[X]) =
      monomial n ((p : A[X]).coeff n) := by
  rw [eq_monomial_coeff (DirectSum.decompose (grading I) p n).property,
    decompose_coeff]

/-- Degree zero is the original base ring, via the actual constant coefficient. -/
def degreeZeroEquiv (I : Ideal A) : grading I 0 ≃+* A where
  toFun p := ((p : reesAlgebra I) : A[X]).coeff 0
  invFun a := homogeneous I 0 ⟨a, by simp⟩
  left_inv p := by
    apply Subtype.ext
    apply Subtype.ext
    exact (eq_monomial_coeff p.property).symm
  right_inv a := by simp [homogeneous]
  map_mul' p q := by
    change (((p : reesAlgebra I) : A[X]) * ((q : reesAlgebra I) : A[X])).coeff 0 = _
    rw [coeff_mul]
    simp
  map_add' p q := by
    change (((p : reesAlgebra I) : A[X]) + ((q : reesAlgebra I) : A[X])).coeff 0 = _
    exact coeff_add _ _ _

@[simp] lemma degreeZeroEquiv_symm_coe (I : Ideal A) (a : A) :
    ((degreeZeroEquiv I).symm a : reesAlgebra I) = algebraMap A (reesAlgebra I) a := by
  apply Subtype.ext
  change monomial 0 a = C a
  exact Polynomial.monomial_zero_left (R := A) (a := a)

@[simp] lemma degreeZeroEquiv_apply (I : Ideal A) (p : grading I 0) :
    degreeZeroEquiv I p = ((p : reesAlgebra I) : A[X]).coeff 0 := rfl

@[simp] lemma degreeZeroEquiv_projZero (I : Ideal A) (p : reesAlgebra I) :
    degreeZeroEquiv I (GradedRing.projZeroRingHom' (grading I) p) =
      (p : A[X]).coeff 0 := by
  exact decompose_coeff I p 0

end reesAlgebra
