/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdjoinRootNormEvaluation
public import Lean.Util.CollectAxioms

/-!
# Consumers of norms in the whole polynomial quotient
-/

@[expose] public noncomputable section

open Polynomial

namespace AglibTest.AdjoinRootNormEvaluation

variable {k : Type*} [Field k]

/-- The zero algebra from the constant monic polynomial is covered as well. -/
theorem constantMonic (a : k) :
    Algebra.norm k (algebraMap k (AdjoinRoot (1 : k[X])) a - AdjoinRoot.root 1) = 1 := by
  simpa only [Polynomial.eval_one] using
    AdjoinRoot.norm_algebraMap_sub_root (1 : k[X]) monic_one a

/-- A double root retains both copies in its determinant norm. -/
theorem repeatedRoot (a b : k) :
    Algebra.norm k (algebraMap k (AdjoinRoot ((X - C b) ^ 2)) a -
      AdjoinRoot.root ((X - C b) ^ 2)) = (a - b) ^ 2 := by
  simpa only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] using
    AdjoinRoot.norm_algebraMap_sub_root ((X - C b) ^ 2) ((monic_X_sub_C b).pow 2) a

/-- Two possibly colliding branches are not replaced by a chosen root field. -/
theorem splitComplement (a b : k) :
    Algebra.norm k (1 - AdjoinRoot.root ((X - C a) * (X - C b))) =
      (1 - a) * (1 - b) := by
  simpa only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
    Polynomial.eval_C] using AdjoinRoot.norm_one_sub_root
      ((X - C a) * (X - C b)) ((monic_X_sub_C a).mul (monic_X_sub_C b))

/-- The whole power-root algebra has the expected complement norm even when
`X^n-a` is reducible or inseparable. -/
theorem powerRootComplement (a : k) (n : ℕ) (hn : n ≠ 0) :
    Algebra.norm k (1 - AdjoinRoot.root ((X : k[X]) ^ n - C a)) = 1 - a := by
  simpa only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, one_pow] using AdjoinRoot.norm_one_sub_root
      ((X : k[X]) ^ n - C a) (monic_X_pow_sub_C a hn)

open Lean in
run_cmd do
  for name in #[``AdjoinRoot.norm_algebraMap_sub_root, ``AdjoinRoot.norm_one_sub_root,
      ``constantMonic, ``repeatedRoot, ``splitComplement, ``powerRootComplement] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Whole monic quotient norms use only standard foundations."

end AglibTest.AdjoinRootNormEvaluation
