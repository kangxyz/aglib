/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdjoinRootScalarBranches
public import Mathlib.Algebra.Squarefree.Basic

/-!
# Exact multiplicities in a product of irreducible polynomial powers

Counting the actual normalized factors extracts the full exponent above each
literal monic irreducible branch. This elementary unique-factorization step is
used after the characteristic-polynomial product identity has been proved.
-/

@[expose] public noncomputable section

open UniqueFactorizationMonoid

namespace Polynomial

variable {k ι : Type*} [Field k] [DecidableEq k]

/-- Count the multiplicity of a literal polynomial in a finite product of
monic irreducible powers. -/
theorem count_normalizedFactors_prod_irreducible_pow
    (s : Finset ι) (p : ι → k[X]) (hp : ∀ i, (p i).Monic ∧ Irreducible (p i))
    (w : ι → ℕ) (q : k[X]) :
    (normalizedFactors (∏ i ∈ s, p i ^ w i)).count q =
      ∑ i ∈ s, if p i = q then w i else 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      normalizedFactors_mul (pow_ne_zero _ (hp a).2.ne_zero)
        (Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hp i).2.ne_zero),
      Multiset.count_add, ih, (hp a).2.normalizedFactors_pow,
      (hp a).1.normalize_eq_self, Multiset.count_replicate]

/-- A squarefree polynomial has each original branch exactly once, so a
product equal to its `e`-th power has total branch exponent exactly `e`. -/
theorem sum_weights_eq_of_prod_eq_squarefree_pow
    [Fintype ι] (P : k[X]) (hP : P.Monic) (hPsq : Squarefree P)
    (p : ι → k[X]) (hp : ∀ i, (p i).Monic ∧ Irreducible (p i))
    (w : ι → ℕ) (e : ℕ) (hprod : ∏ i, p i ^ w i = P ^ e)
    (q : AdjoinRoot.IrreducibleBranch P) :
    (∑ i, if p i = q.val.val then w i else 0) = e := by
  classical
  have hc := congrArg (fun f : k[X] => (normalizedFactors f).count q.val.val) hprod
  rw [count_normalizedFactors_prod_irreducible_pow Finset.univ p hp w,
    normalizedFactors_pow, Multiset.count_nsmul] at hc
  have hqmem : q.val.val ∈ normalizedFactors P :=
    (Polynomial.mem_normalizedFactors_iff hP.ne_zero).mpr
      ⟨q.val.property.2, q.val.property.1, q.property⟩
  have hcount : (normalizedFactors P).count q.val.val = 1 :=
    Multiset.count_eq_one_of_mem
      ((squarefree_iff_nodup_normalizedFactors hP.ne_zero).mp hPsq) hqmem
  simpa only [hcount, mul_one] using hc

end Polynomial
