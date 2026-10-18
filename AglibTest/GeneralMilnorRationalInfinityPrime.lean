/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalInfinityPrime

/-! # Direct consumers of the actual rational infinity norm square -/

@[expose] public noncomputable section

namespace AglibTest.GeneralMilnorRationalInfinityPrime

open MilnorK
open Polynomial PolynomialResidue PolynomialNorm

/-- Only the original prime normal coefficient extension is assumed. -/
theorem actual_infinity_norm_square {k : Type*} [Field k] [CharZero k]
    (p : MonicIrreducible k) [Normal k (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime) (n : ℕ)
    (x : K (RatFunc (AdjoinRoot p.val)) (n + 1)) :
    InfinityResidue.residue k n (rationalFunctionNorm (n + 1) p x) =
      polynomialNorm n p (InfinityResidue.residue (AdjoinRoot p.val) n x) :=
  infinityResidue_rationalFunctionNorm_prime p hp n x

open Lean in
run_cmd do
  for name in #[``infinityResidue_rationalFunctionNorm_prime,
      ``infinityResidue_comp_rationalFunctionNorm_prime, ``actual_infinity_norm_square] do
    for dependency in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
        throwError "{name} depends on unsupported assumption {dependency}"
  logInfo "The actual rational infinity square uses only standard foundations."

end AglibTest.GeneralMilnorRationalInfinityPrime
