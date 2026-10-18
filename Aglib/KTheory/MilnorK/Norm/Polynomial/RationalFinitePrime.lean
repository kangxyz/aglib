/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalBaseChange
public import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalBranchLinear
public import Aglib.KTheory.MilnorK.Residue.Polynomial.TensorBranches
public import Aglib.KTheory.MilnorK.Norm.Polynomial.PrimeInduction

/-!
# The full finite-place square for a normal-prime rational norm

Restricting to the original residue field turns the lower place into a linear
place with identity residue map. The full coefficient branch sum is then matched
by the actual tensor-swap quotient equivalences. Both split and irreducible
constant branches are retained. No norm tower or independence law is assumed.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue

variable {k : Type*} [Field k] [CharZero k]

local instance {L : Type*} [Field L] (a : L) :
    Fact (Irreducible (X - C a)) := ⟨irreducible_X_sub_C a⟩

open scoped Classical in
/-- The original finite-place residue of the rational normal-prime norm is the
full sum of the matched branch norms of the original upper residues. -/
theorem residueAt_rationalFunctionNorm_prime
    (p : MonicIrreducible k) [Normal k (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime) (h : MonicIrreducible k) (n : ℕ)
    (x : K (RatFunc (AdjoinRoot p.val)) (n + 1)) :
    residueAt h.val n (rationalFunctionNorm (n + 1) p x) =
      ∑ q ∈ (placesAbove (algebraMap k (AdjoinRoot p.val)) h).attach,
        polynomialNorm n
          (AdjoinRoot.tensorSwapBranchEquiv p.val h.val
            ⟨q.val, (mem_placesAbove _ _ _).mp q.property⟩).val
          (map n (AdjoinRoot.tensorSwapBranchRingEquiv p.val h.val
            ⟨q.val, (mem_placesAbove _ _ _).mp q.property⟩).toRingHom
            (residueAt q.val.val n x)) := by
  classical
  let : CharZero (AdjoinRoot p.val) :=
    charZero_of_injective_algebraMap (algebraMap k (AdjoinRoot p.val)).injective
  let B := (placesAboveBranchEquiv (algebraMap k (AdjoinRoot p.val)) h).trans
    ((AdjoinRoot.tensorSwapBranchEquiv p.val h.val).trans
      (placesAboveBranchEquiv (algebraMap k (AdjoinRoot h.val)) p).symm)
  rw [residueAt_eq_linearPlace h.val, rationalFunctionNorm_restrict]
  simp only [map_sum, Finset.attach_eq_univ]
  symm
  apply Fintype.sum_equiv B
  intro q
  let qb : AdjoinRoot.IrreducibleBranch (h.val.map (algebraMap k (AdjoinRoot p.val))) :=
    placesAboveBranchEquiv (algebraMap k (AdjoinRoot p.val)) h q
  let rb := AdjoinRoot.tensorSwapBranchEquiv p.val h.val qb
  change polynomialNorm n rb.val
      (map n (AdjoinRoot.tensorSwapBranchRingEquiv p.val h.val qb).toRingHom
        (residueAt qb.val.val n x)) =
    map n (linearRootEquiv (AdjoinRoot.root h.val)).toRingHom
      (residueAt (X - C (AdjoinRoot.root h.val)) n
        (rationalFunctionNorm (n + 1) rb.val
          (map (n + 1) (fractionMap (adjoinRootMap
            (algebraMap k (AdjoinRoot h.val)) p.val rb.val.val rb.property)) x)))
  rw [residueAt_linear_rationalFunctionNorm_scalarBranch p hp rb]
  apply congrArg (polynomialNorm n rb.val)
  exact residueAt_tensorBranch_linear p.val h.val qb n x

open scoped Classical in
/-- The finite-place square as an equality of actual integer-linear maps. -/
theorem residueAt_comp_rationalFunctionNorm_prime
    (p : MonicIrreducible k) [Normal k (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime) (h : MonicIrreducible k) (n : ℕ) :
    (residueAt h.val n).comp (rationalFunctionNorm (n + 1) p) =
      ∑ q ∈ (placesAbove (algebraMap k (AdjoinRoot p.val)) h).attach,
        (polynomialNorm n
          (AdjoinRoot.tensorSwapBranchEquiv p.val h.val
            ⟨q.val, (mem_placesAbove _ _ _).mp q.property⟩).val).comp
          ((map n (AdjoinRoot.tensorSwapBranchRingEquiv p.val h.val
            ⟨q.val, (mem_placesAbove _ _ _).mp q.property⟩).toRingHom).comp
            (residueAt q.val.val n)) := by
  apply LinearMap.ext
  intro x
  simpa only [LinearMap.comp_apply, LinearMap.sum_apply] using
    residueAt_rationalFunctionNorm_prime p hp h n x

end MilnorK.PolynomialNorm
