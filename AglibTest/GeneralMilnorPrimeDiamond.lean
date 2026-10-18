/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.PrimeDiamond

/-! # Consumers of the actual normal-prime norm diamond -/

@[expose] public noncomputable section

namespace AglibTest.GeneralMilnorPrimeDiamond

open MilnorK
open Polynomial PolynomialResidue PolynomialNorm

open scoped Classical in
/-- An arbitrary upper quotient class has an actual supported lift, not a compatibility witness. -/
theorem actual_single_place_lift {k : Type*} [Field k] [CharZero k]
    (p : MonicIrreducible k) [Normal k (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime) (n : ℕ)
    (q : MonicIrreducible (AdjoinRoot p.val)) (z : K (AdjoinRoot q.val) n) :
    ∃ x : K (RatFunc (AdjoinRoot p.val)) (n + 1),
      totalResidue n x = DFinsupp.single q z ∧
      polynomialNorm n p (polynomialNorm n q z) =
        -InfinityResidue.residue k n (rationalFunctionNorm (n + 1) p x) :=
  exists_single_place_rational_norm_lift p hp n q z

/-- The original iterated norms agree on every actual tensor branch. -/
theorem actual_prime_diamond {k : Type*} [Field k] [CharZero k]
    (p : MonicIrreducible k) [Normal k (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime) (h : MonicIrreducible k)
    (q : AdjoinRoot.IrreducibleBranch (h.val.map (algebraMap k (AdjoinRoot p.val))))
    (n : ℕ) (z : K (AdjoinRoot q.val.val) n) :
    polynomialNorm n p (polynomialNorm n q.val z) =
      polynomialNorm n h
        (polynomialNorm n (AdjoinRoot.tensorSwapBranchEquiv p.val h.val q).val
          (map n (AdjoinRoot.tensorSwapBranchRingEquiv p.val h.val q).toRingHom z)) :=
  polynomialNorm_prime_diamond p hp h q n z

open Lean in
run_cmd do
  for name in #[``polynomialNorm_polynomialNorm_eq_neg_infinity_of_lift,
      ``exists_single_place_rational_norm_lift, ``tensorBranch_not_mem_placesAbove,
      ``tensorBranchResidueSum_single_place, ``actual_single_place_lift,
      ``totalResidue_rationalFunctionNorm_single, ``polynomialNorm_prime_diamond,
      ``actual_prime_diamond] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "Actual normal-prime norm diamond uses only standard foundations."

end AglibTest.GeneralMilnorPrimeDiamond
