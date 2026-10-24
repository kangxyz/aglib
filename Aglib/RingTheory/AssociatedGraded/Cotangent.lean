/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AssociatedGraded.Basic
public import Aglib.RingTheory.ReesAlgebra.DegreeOne
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The canonical cotangent map to the actual associated graded ring

The original quotient A/I acts on the actual Rees quotient defining the
associated graded ring. The degree-one symbol factors through the original
cotangent quotient I/I² and extends to its symmetric algebra. The original
symbol formula is retained, and Rees degree-one generation proves the
canonical symmetric-algebra map surjective.

The construction works for arbitrary commutative rings and ideals. No
coefficient section, Noetherian, rational/Gorenstein, tangent-kernel or
surjectivity hypothesis is assumed. The full quadratic tangent-kernel
calculation requires its separate Hilbert-function and geometric suppliers.
-/

@[expose] public noncomputable section
set_option autoImplicit false

universe u

open Polynomial

namespace Ideal

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The actual Rees degree-one inclusion, with its original scalar action. -/
def reesDegreeOneLinear : I →ₗ[A] reesAlgebra I where
  toFun := reesAlgebra.degreeOne I
  map_add' a b := by
    apply Subtype.ext
    change Polynomial.monomial 1 ((a : A) + b) =
      Polynomial.monomial 1 (a : A) + Polynomial.monomial 1 (b : A)
    exact map_add (Polynomial.monomial 1) (a : A) (b : A)
  map_smul' r a := by
    apply Subtype.ext
    change Polynomial.monomial 1 (r • (a : A)) = r • Polynomial.monomial 1 (a : A)
    exact (Polynomial.monomial 1).map_smul r (a : A)

/-- The original degree-one symbol before quotienting the maximal ideal by its square. -/
def associatedGradedDegreeOneLinear : I →ₗ[A] I.associatedGraded :=
  (Ideal.Quotient.mkₐ A I.associatedGradedIdeal).toLinearMap.comp (reesDegreeOneLinear I)

/-- The original symbol vanishes precisely on the actual square of the ideal. -/
theorem associatedGradedDegreeOneLinear_eq_zero_iff (a : I) :
    associatedGradedDegreeOneLinear I a = 0 ↔ (a : A) ∈ I ^ 2 := by
  change Ideal.Quotient.mk I.associatedGradedIdeal (reesAlgebra.degreeOne I a) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem, I.mem_associatedGradedIdeal_iff]
  constructor
  · intro h
    simpa [reesAlgebra.degreeOne_val] using h 1
  · intro ha n
    by_cases hn : n = 1
    · subst n
      simpa [reesAlgebra.degreeOne_val] using ha
    · rw [reesAlgebra.degreeOne_val, Polynomial.coeff_monomial, ite_eq_right (Ne.symm hn)]
      exact (I ^ (n + 1)).zero_mem

/-- The actual cotangent quotient maps to the actual associated graded ring. -/
def cotangentToAssociatedGraded : I.Cotangent →ₗ[A] I.associatedGraded :=
  ((LinearMap.ker I.toCotangent).liftQ (associatedGradedDegreeOneLinear I) (by
    intro a ha
    exact (associatedGradedDegreeOneLinear_eq_zero_iff I a).mpr
      (I.mem_toCotangent_ker.mp ha))).comp
    (I.toCotangent.quotKerEquivOfSurjective I.toCotangent_surjective).symm.toLinearMap

/-- The cotangent map retains the exact original degree-one Rees symbol. -/
theorem cotangentToAssociatedGraded_toCotangent (a : I) :
    cotangentToAssociatedGraded I (I.toCotangent a) =
      Ideal.Quotient.mk I.associatedGradedIdeal (reesAlgebra.degreeOne I a) := by
  simp only [cotangentToAssociatedGraded, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  rfl

/-- The original coefficient quotient acts on the actual associated graded ring. -/
def associatedGradedCoefficientMap : (A ⧸ I) →+* I.associatedGraded :=
  Ideal.Quotient.lift I (algebraMap A I.associatedGraded) (by
    intro a ha
    change Ideal.Quotient.mk I.associatedGradedIdeal (algebraMap A (reesAlgebra I) a) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.mem_map_of_mem (algebraMap A (reesAlgebra I)) ha))

/-- The coefficient quotient acts by the original coefficient map on every original scalar. -/
theorem associatedGradedCoefficientMap_mk (a : A) :
    associatedGradedCoefficientMap I (Ideal.Quotient.mk I a) =
      algebraMap A I.associatedGraded a := rfl

/-- The canonical algebra action of the original coefficient quotient. -/
instance associatedGradedQuotientAlgebra : Algebra (A ⧸ I) I.associatedGraded :=
  @RingHom.toAlgebra' (A ⧸ I) I.associatedGraded (Ideal.Quotient.commSemiring I)
    (Ideal.Quotient.semiring I.associatedGradedIdeal)
    (associatedGradedCoefficientMap I)
    (fun r x => (Ideal.Quotient.commSemiring I.associatedGradedIdeal).mul_comm
      (associatedGradedCoefficientMap I r) x)

/-- The quotient action retains the original scalar tower. -/
instance associatedGradedQuotientScalarTower : IsScalarTower A (A ⧸ I) I.associatedGraded := by
  apply IsScalarTower.of_algebraMap_eq'
  apply RingHom.ext
  intro a
  change algebraMap A I.associatedGraded a =
    associatedGradedCoefficientMap I (Ideal.Quotient.mk I a)
  exact (associatedGradedCoefficientMap_mk I a).symm

/-- The canonical cotangent symbol is linear over the original coefficient quotient. -/
def cotangentSymbol : I.Cotangent →ₗ[A ⧸ I] I.associatedGraded :=
  (cotangentToAssociatedGraded I).extendScalarsOfSurjective Ideal.Quotient.mk_surjective

/-- The canonical coefficient-linear symbol retains each original ideal element. -/
theorem cotangentSymbol_toCotangent (a : I) :
    cotangentSymbol I (I.toCotangent a) =
      Ideal.Quotient.mk I.associatedGradedIdeal (reesAlgebra.degreeOne I a) :=
  cotangentToAssociatedGraded_toCotangent I a

/-- The canonical symmetric-algebra tangent map of the actual ideal filtration. -/
def symmetricCotangentMap : SymmetricAlgebra (A ⧸ I) I.Cotangent →ₐ[A ⧸ I] I.associatedGraded := by
  let _ : CommSemiring I.associatedGraded := Ideal.Quotient.commSemiring I.associatedGradedIdeal
  exact SymmetricAlgebra.lift (R := A ⧸ I) (M := I.Cotangent) (A := I.associatedGraded)
    (cotangentSymbol I)

/-- The intrinsic tangent map uses the literal original degree-one symbol map. -/
theorem symmetricCotangentMap_iota_toCotangent (a : I) :
    symmetricCotangentMap I (SymmetricAlgebra.ι (A ⧸ I) I.Cotangent (I.toCotangent a)) =
      Ideal.Quotient.mk I.associatedGradedIdeal (reesAlgebra.degreeOne I a) := by
  rw [symmetricCotangentMap, SymmetricAlgebra.lift_ι_apply, cotangentSymbol_toCotangent]

/-- The canonical tangent map is onto the actual associated graded ring.
The proof uses the original Rees degree-one generation and original quotient map. -/
theorem symmetricCotangentMap_surjective : Function.Surjective (symmetricCotangentMap I) := by
  let P := symmetricCotangentMap I
  let N : Subalgebra A (reesAlgebra I) :=
    (P.range.restrictScalars A).comap (Ideal.Quotient.mkₐ A I.associatedGradedIdeal)
  have h1 : reesAlgebra.grading I 1 ≤ N.toSubmodule := by
    intro p hp
    let a : I := ⟨(p : A[X]).coeff 1, by simpa only [pow_one] using p.property 1⟩
    have he : reesAlgebra.degreeOne I a = p := by
      apply Subtype.ext
      exact (reesAlgebra.eq_monomial_coeff hp).symm
    change Ideal.Quotient.mk I.associatedGradedIdeal p ∈ P.range
    refine ⟨SymmetricAlgebra.ι (A ⧸ I) I.Cotangent (I.toCotangent a), ?_⟩
    exact (symmetricCotangentMap_iota_toCotangent I a).trans
      (congrArg (Ideal.Quotient.mk I.associatedGradedIdeal) he)
  have hpow (n : ℕ) : (reesAlgebra.grading I 1) ^ n ≤ N.toSubmodule := by
    induction n with
    | zero =>
      rw [pow_zero, Submodule.one_eq_span]
      apply Submodule.span_le.mpr
      rintro p (rfl : p = 1)
      exact N.one_mem
    | succ n ih =>
      rw [pow_succ']
      apply Submodule.mul_le.mpr
      intro p hp q hq
      exact N.mul_mem (h1 hp) (ih hq)
  have hhom (n : ℕ) : reesAlgebra.grading I n ≤ N.toSubmodule := by
    rw [← reesAlgebra.grading_one_pow I n]
    exact hpow n
  have hN (p : reesAlgebra I) : p ∈ N := by
    induction p using DirectSum.Decomposition.inductionOn (reesAlgebra.grading I) with
    | zero => exact N.zero_mem
    | @homogeneous n p => exact hhom n p.property
    | add p q hp hq => exact N.add_mem hp hq
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact hN p

end Ideal
