/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Polynomial.Lifts
public import Mathlib.FieldTheory.Minpoly.Field
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Monic lifts of equations over a residue field

Surjectivity of the coefficient quotient, rather than a coefficient-field
section, produces monic lifts with exactly the original degree. The literal
coefficient triangle identifies evaluation after reduction. No flatness or
domain condition on the original algebra is needed.
-/

@[expose] public section

noncomputable section

universe u v w t

namespace LocalResidueMonicEquations

variable {R : Type u} [CommRing R] {k : Type v} [Field k]
variable {B : Type w} [CommRing B] [Algebra R B]
variable (q : Ideal B) [q.IsPrime] [Algebra k (B ⧸ q)]
variable (f : R →+* k) (hf : Function.Surjective f)
variable (htriangle : (algebraMap k (B ⧸ q)).comp f = algebraMap R (B ⧸ q))

include hf htriangle

/-- A residue-integral coordinate has a genuine positive-degree monic equation
upstairs whose evaluation lies in the selected prime. -/
theorem exists_monic_lift (z : B) (hz : IsIntegral k (Ideal.Quotient.mk q z)) :
    ∃ Q : Polynomial R, Q.Monic ∧ 0 < Q.natDegree ∧
      Q.map f = minpoly k (Ideal.Quotient.mk q z) ∧ Polynomial.aeval z Q ∈ q := by
  obtain ⟨Q, hQ, hd, hm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective hf (minpoly k (Ideal.Quotient.mk q z)))
    (minpoly.monic hz)
  refine ⟨Q, hm, hd ▸ minpoly.natDegree_pos hz, hQ, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have heval : (Ideal.Quotient.mk q) (Polynomial.aeval z Q) =
      Polynomial.aeval (Ideal.Quotient.mk q z) (Q.map f) := by
    change (Ideal.Quotient.mk q) (Q.eval₂ (algebraMap R B) z) =
      (Q.map f).eval₂ (algebraMap k (B ⧸ q)) (Ideal.Quotient.mk q z)
    rw [Polynomial.hom_eval₂, Polynomial.eval₂_map, htriangle]
    rfl
  rw [heval, hQ]
  exact minpoly.aeval k (Ideal.Quotient.mk q z)

/-- All residue-coordinate equations are lifted independently, without asking
for a ring section of the residue map. -/
theorem exists_equations {ι : Type t} (z : ι → B)
    (hz : ∀ i, IsIntegral k (Ideal.Quotient.mk q (z i))) :
    ∃ Q : ι → Polynomial R, (∀ i, (Q i).Monic) ∧
      (∀ i, 0 < (Q i).natDegree) ∧
      (∀ i, (Q i).map f = minpoly k (Ideal.Quotient.mk q (z i))) ∧
      (∀ i, Polynomial.aeval (z i) (Q i) ∈ q) := by
  classical
  choose Q hm hd he hq using fun i => exists_monic_lift q f hf htriangle (z i) (hz i)
  exact ⟨Q, hm, hd, he, hq⟩

end LocalResidueMonicEquations
