/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.ReesAlgebra.Grading
public import Aglib.RingTheory.GradedAlgebra.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian

/-!
# The associated graded ring as a native Rees quotient

The ideal extended from degree zero has exactly the polynomials whose degree-n
coefficient lies in the next ideal power. Thus the quotient retains the native
Rees grading, without any flatness hypothesis.
-/

@[expose] public noncomputable section

open Polynomial DirectSum
universe u
namespace Ideal
variable {A : Type u} [CommRing A] (I : Ideal A)

/-- The ideal of the Rees algebra extended from the original degree-zero ideal. -/
def associatedGradedIdeal : Ideal (reesAlgebra I) :=
  I.map (algebraMap A (reesAlgebra I))

/-- The coefficientwise description of the ideal defining the associated graded. -/
def reesSuccessorIdeal : Ideal (reesAlgebra I) where
  carrier := {p | ∀ n, (p : A[X]).coeff n ∈ I ^ (n + 1)}
  zero_mem' := by intro n; simp
  add_mem' := by
    intro p q hp hq n
    change ((p : A[X]) + (q : A[X])).coeff n ∈ I ^ (n + 1)
    rw [coeff_add]
    exact (I ^ (n + 1)).add_mem (hp n) (hq n)
  smul_mem' := by
    intro p q hq n
    change ((p : A[X]) * (q : A[X])).coeff n ∈ I ^ (n + 1)
    rw [coeff_mul]
    apply Ideal.sum_mem
    rintro ⟨i, j⟩ hij
    have he : i + (j + 1) = n + 1 := by
      rw [← Nat.add_assoc, Finset.mem_antidiagonal.mp hij]
    rw [← he, pow_add]
    exact Ideal.mul_mem_mul (p.property i) (hq j)

lemma associatedGradedIdeal_le_reesSuccessorIdeal :
    I.associatedGradedIdeal ≤ I.reesSuccessorIdeal := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro a ha n
  change (C a).coeff n ∈ I ^ (n + 1)
  by_cases hn : n = 0
  · subst n; simpa using ha
  · simp [coeff_C, hn]

lemma homogeneous_mem_associatedGradedIdeal (n : ℕ) (a : ↥(I ^ n : Ideal A))
    (ha : (a : A) ∈ I ^ (n + 1)) :
    (reesAlgebra.homogeneous I n a : reesAlgebra I) ∈ I.associatedGradedIdeal := by
  have h : ∀ (x : A) (hx : x ∈ I * I ^ n),
      (reesAlgebra.homogeneous I n ⟨x, Ideal.mul_le_right hx⟩ : reesAlgebra I) ∈
        I.associatedGradedIdeal := by
    intro x hx
    refine Submodule.smul_induction_on' hx ?_ ?_
    · intro r hr s hs
      have hm := (I.associatedGradedIdeal).mul_mem_left
        (reesAlgebra.homogeneous I n ⟨s, hs⟩ : reesAlgebra I)
        (Ideal.mem_map_of_mem (algebraMap A (reesAlgebra I)) hr)
      convert hm using 1
      apply Subtype.ext
      change monomial n (r * s) = monomial n s * C r
      simp [mul_comm]
    · intro x hx y hy ihx ihy
      have hm := (I.associatedGradedIdeal).add_mem ihx ihy
      convert hm using 1
      apply Subtype.ext
      exact map_add (monomial n) x y
  exact h a (by simpa [pow_succ'] using ha)

lemma associatedGradedIdeal_eq_reesSuccessorIdeal :
    I.associatedGradedIdeal = I.reesSuccessorIdeal := by
  apply le_antisymm I.associatedGradedIdeal_le_reesSuccessorIdeal
  intro p hp
  have hsum : p = ∑ n ∈ (p : A[X]).support,
      (reesAlgebra.homogeneous I n ⟨(p : A[X]).coeff n, p.property n⟩ :
        reesAlgebra I) := by
    apply Subtype.ext
    simpa only [AddSubmonoidClass.coe_finsetSum, reesAlgebra.homogeneous] using
      (p : A[X]).as_sum_support
  rw [hsum]
  apply Ideal.sum_mem
  intro n hn
  exact I.homogeneous_mem_associatedGradedIdeal n _ (hp n)

lemma mem_associatedGradedIdeal_iff (p : reesAlgebra I) :
    p ∈ I.associatedGradedIdeal ↔ ∀ n, (p : A[X]).coeff n ∈ I ^ (n + 1) := by
  rw [I.associatedGradedIdeal_eq_reesSuccessorIdeal]
  rfl

/-- The defining ideal is homogeneous for the original Rees grading. -/
lemma associatedGradedIdeal_isHomogeneous :
    I.associatedGradedIdeal.IsHomogeneous (reesAlgebra.grading I) := by
  intro n p hp
  rw [I.mem_associatedGradedIdeal_iff] at hp ⊢
  intro m
  rw [reesAlgebra.decompose_val]
  by_cases h : n = m
  · subst m; simpa using hp n
  · simp [coeff_monomial, h]

/-- The associated graded ring of an ideal, as the native Rees algebra quotient. -/
abbrev associatedGraded := reesAlgebra I ⧸ I.associatedGradedIdeal

/-- The actual image of each Rees homogeneous component in the associated graded. -/
def associatedGradedGrading (n : ℕ) : Submodule A I.associatedGraded :=
  GradedAlgebra.Quotient.grading (reesAlgebra.grading I) I.associatedGradedIdeal n

instance : GradedAlgebra I.associatedGradedGrading :=
  GradedAlgebra.Quotient.gradedAlgebra (reesAlgebra.grading I)
    I.associatedGradedIdeal I.associatedGradedIdeal_isHomogeneous

instance [IsNoetherianRing A] : IsNoetherianRing I.associatedGraded := inferInstance

end Ideal
