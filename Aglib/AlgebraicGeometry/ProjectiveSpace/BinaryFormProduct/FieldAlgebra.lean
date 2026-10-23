/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Algebra
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Polynomial.Div

/-!
# Finite-or-infinite factor coordinates over a field

`none` denotes the original vector `(0,1)`, and `some a` denotes `(1,a)`.
Factoring a degree-at-most-`n` polynomial into exactly `n` such factors
retains the factors at infinity. Finite factor coordinates in a fixed
nonzero polynomial fibre lie in its finite root set.
-/

@[expose] public noncomputable section

open scoped BigOperators
open Polynomial

namespace AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Field

universe u

variable {K : Type u} [Field K] {n : ℕ}

/-- The first coordinate of a finite-or-infinite original pair. -/
def first : Option K → K
  | none => 0
  | some _ => 1

/-- The second coordinate of a finite-or-infinite original pair. -/
def second : Option K → K
  | none => 1
  | some a => a

/-- The original coefficient polynomial of the normalized factor family. -/
def normalizedPolynomial (a : Fin n → Option K) : K[X] :=
  polynomial (fun i => first (a i)) (fun i => second (a i))

@[simp]
theorem linear_none : linear (first (none : Option K)) (second none) = 1 := by
  simp [first, second, linear]

@[simp]
theorem linear_some (a : K) : linear (first (some a)) (second (some a)) = X + C a := by
  simp [first, second, linear]

theorem normalizedPolynomial_succ (a : Fin (n + 1) → Option K) :
    normalizedPolynomial a = linear (first (a 0)) (second (a 0)) *
      normalizedPolynomial (fun i : Fin n => a i.succ) :=
  polynomial_succ _ _

@[simp]
theorem normalizedPolynomial_zero (a : Fin 0 → Option K) : normalizedPolynomial a = 1 :=
  polynomial_zero _ _

theorem normalizedPolynomial_ne_zero (a : Fin n → Option K) :
    normalizedPolynomial a ≠ 0 := by
  change (∏ i, linear (first (a i)) (second (a i))) ≠ 0
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  cases a i with
  | none => simp
  | some b => simp [linear_some, Polynomial.X_add_C_ne_zero]

/-- Every nonzero polynomial of degree at most `n` has exactly `n` original
finite-or-infinite factors over an algebraically closed field. -/
theorem exists_normalized_factorization [IsAlgClosed K] (p : K[X]) (hp : p ≠ 0)
    (hdegree : p.natDegree ≤ n) :
    ∃ (a : Fin n → Option K) (c : K), c ≠ 0 ∧
      p = C c * normalizedPolynomial a := by
  induction n generalizing p with
  | zero =>
      have hd : p.natDegree = 0 := Nat.eq_zero_of_le_zero hdegree
      have hc : p.coeff 0 ≠ 0 := by
        intro hz
        apply hp
        rw [Polynomial.eq_C_of_natDegree_eq_zero hd, hz, map_zero]
      refine ⟨Fin.elim0, p.coeff 0, hc, ?_⟩
      rw [normalizedPolynomial_zero, mul_one]
      exact Polynomial.eq_C_of_natDegree_eq_zero hd
  | succ n ih =>
      by_cases hd : p.natDegree = 0
      · obtain ⟨a, c, hc, ha⟩ := ih p hp (by omega)
        refine ⟨Fin.cons none a, c, hc, ?_⟩
        simpa only [normalizedPolynomial_succ, Fin.cons_zero, Fin.cons_succ,
          linear_none, one_mul] using ha
      · obtain ⟨r, hr⟩ := IsAlgClosed.exists_root p
          (Polynomial.degree_ne_of_natDegree_ne hd)
        obtain ⟨q, hq⟩ := Polynomial.dvd_iff_isRoot.mpr hr
        have hqn : q ≠ 0 := by
          intro hz
          exact hp (hq.trans (by rw [hz, mul_zero]))
        have hqd : q.natDegree ≤ n := by
          rw [hq, Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero r) hqn,
            Polynomial.natDegree_X_sub_C] at hdegree
          omega
        obtain ⟨a, c, hc, ha⟩ := ih q hqn hqd
        refine ⟨Fin.cons (some (-r)) a, c, hc, ?_⟩
        rw [hq, ha, normalizedPolynomial_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, linear_some, map_neg]
        simp only [sub_eq_add_neg]
        ring

/-- A finite normalized factor supplies its actual negative parameter as a root. -/
theorem isRoot_of_finite_factor (a : Fin n → Option K) (i : Fin n) (b : K)
    (hi : a i = some b) : (normalizedPolynomial a).IsRoot (-b) := by
  change (polynomial (fun j => first (a j)) (fun j => second (a j))).eval (-b) = 0
  rw [polynomial, Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp [hi, linear_some]

/-- The exact finite root bound for any normalized factor of a fixed nonzero polynomial. -/
theorem neg_mem_roots_of_finite_factor (a : Fin n → Option K) (p : K[X])
    (hp : p ≠ 0) (c : K) (hc : c ≠ 0)
    (h : normalizedPolynomial a = C c * p) (i : Fin n) (b : K)
    (hi : a i = some b) : -b ∈ p.roots := by
  apply (Polynomial.mem_roots hp).mpr
  have hr := isRoot_of_finite_factor a i b hi
  change (normalizedPolynomial a).eval (-b) = 0 at hr
  rw [h, Polynomial.eval_mul, Polynomial.eval_C] at hr
  exact (mul_eq_zero.mp hr).resolve_left hc

/-- All finite-or-infinite coordinates allowed by a fixed polynomial form a finite set. -/
def allowedCoordinates (p : K[X]) : Set (Option K) :=
  {none} ∪ (fun r : K => some (-r)) '' {r : K | r ∈ p.roots}

theorem allowedCoordinates_finite (p : K[X]) : (allowedCoordinates p).Finite := by
  classical
  have h : {r : K | r ∈ p.roots}.Finite := by
    simpa only [Multiset.coe_toFinset] using p.roots.toFinset.finite_toSet
  exact (Set.finite_singleton none).union (h.image _)

theorem coordinate_mem_allowed (a : Fin n → Option K) (p : K[X]) (hp : p ≠ 0)
    (c : K) (hc : c ≠ 0) (h : normalizedPolynomial a = C c * p) (i : Fin n) :
    a i ∈ allowedCoordinates p := by
  cases hi : a i with
  | none => exact Or.inl rfl
  | some b =>
      right
      exact ⟨-b, by simpa using neg_mem_roots_of_finite_factor a p hp c hc h i b hi,
        by simp⟩

/-- A fixed nonzero polynomial has only finitely many ordered normalized factor
families of length `n`, even when factors repeat or the characteristic divides `n!`. -/
theorem finite_normalized_factor_fiber (p : K[X]) (hp : p ≠ 0) :
    Finite {a : Fin n → Option K // ∃ c : K, c ≠ 0 ∧
      normalizedPolynomial a = C c * p} := by
  have : Finite (allowedCoordinates p) := (allowedCoordinates_finite p).to_subtype
  let encode : {a : Fin n → Option K // ∃ c : K, c ≠ 0 ∧
      normalizedPolynomial a = C c * p} → (Fin n → allowedCoordinates p) := fun a i =>
    ⟨a.val i, by
      obtain ⟨c, hc, ha⟩ := a.property
      exact coordinate_mem_allowed a.val p hp c hc ha i⟩
  apply Finite.of_injective encode
  intro a b hab
  apply Subtype.ext
  funext i
  exact congrArg (fun v : Fin n → allowedCoordinates p => (v i).val) hab

end AlgebraicGeometry.ProjectiveSpace.BinaryFormProduct.Field
