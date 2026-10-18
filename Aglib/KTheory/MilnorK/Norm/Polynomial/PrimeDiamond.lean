/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalInfinityPrime
public import Aglib.KTheory.MilnorK.Norm.Polynomial.RationalFinitePrime
public import Aglib.RingTheory.AdjoinRootTensorBranches

/-!
# The actual normal-prime norm diamond

Surjectivity of the original total residue map supplies a lift supported at a
single upper place. The proved infinity square computes the iterated norm as
minus infinity of its actual rational-function norm. The lift is not an assumed
compatibility datum, and the rational norm is the constructed polynomial norm.
The finite-place square identifies the contracted singleton residue, so the
original lift characterization of the norm closes the tensor-matched diamond.
-/

@[expose] public noncomputable section

namespace MilnorK.PolynomialNorm

open Polynomial Polynomial.LocalResidue PolynomialResidue

variable {k : Type*} [Field k] [CharZero k]

open scoped Classical in
/-- An actual upper single-place lift computes the first path of the norm diamond. -/
theorem polynomialNorm_polynomialNorm_eq_neg_infinity_of_lift
    (p : MonicIrreducible k) [Normal k (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime) (n : ℕ)
    (q : MonicIrreducible (AdjoinRoot p.val)) (z : K (AdjoinRoot q.val) n)
    (x : K (RatFunc (AdjoinRoot p.val)) (n + 1))
    (hx : totalResidue n x = DFinsupp.single q z) :
    polynomialNorm n p (polynomialNorm n q z) =
      -InfinityResidue.residue k n (rationalFunctionNorm (n + 1) p x) := by
  rw [polynomialNorm_eq_neg_residue_of_lift n q z x hx, map_neg,
    infinityResidue_rationalFunctionNorm_prime p hp]

open scoped Classical in
/-- Every class admits an actual rational lift with its iterated norm already computed. -/
theorem exists_single_place_rational_norm_lift
    (p : MonicIrreducible k) [Normal k (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime) (n : ℕ)
    (q : MonicIrreducible (AdjoinRoot p.val)) (z : K (AdjoinRoot q.val) n) :
    ∃ x : K (RatFunc (AdjoinRoot p.val)) (n + 1),
      totalResidue n x = DFinsupp.single q z ∧
      polynomialNorm n p (polynomialNorm n q z) =
        -InfinityResidue.residue k n (rationalFunctionNorm (n + 1) p x) := by
  obtain ⟨x, hx⟩ := totalResidue_surjective n (DFinsupp.single q z)
  exact ⟨x, hx, polynomialNorm_polynomialNorm_eq_neg_infinity_of_lift p hp n q z x hx⟩

omit [CharZero k] in
/-- A chosen upper branch cannot lie over a different finite lower place. -/
theorem tensorBranch_not_mem_placesAbove
    (p h : MonicIrreducible k)
    (q : AdjoinRoot.IrreducibleBranch (h.val.map (algebraMap k (AdjoinRoot p.val))))
    (h' : MonicIrreducible k) (hne : h' ≠ h) :
    q.val ∉ placesAbove (algebraMap k (AdjoinRoot p.val)) h' := by
  intro hq
  apply hne
  apply Subtype.ext
  exact monic_irreducible_eq_of_dvd_map (algebraMap k (AdjoinRoot p.val))
    h'.val h.val q.val.val h'.property.1 h.property.1
    ((mem_placesAbove _ _ _).mp hq) q.property

/-- The literal finite branch sum, without any asserted norm compatibility. -/
def tensorBranchResidueSum (p h : MonicIrreducible k) (n : ℕ)
    (x : K (RatFunc (AdjoinRoot p.val)) (n + 1)) : K (AdjoinRoot h.val) n := by
  classical
  exact ∑ q ∈ (placesAbove (algebraMap k (AdjoinRoot p.val)) h).attach,
    polynomialNorm n
      (AdjoinRoot.tensorSwapBranchEquiv p.val h.val
        ⟨q.val, (mem_placesAbove _ _ _).mp q.property⟩).val
      (map n (AdjoinRoot.tensorSwapBranchRingEquiv p.val h.val
        ⟨q.val, (mem_placesAbove _ _ _).mp q.property⟩).toRingHom
        (residueAt q.val.val n x))

omit [CharZero k] in
open scoped Classical in
/-- The actual branch sum of a single-place lift is supported only at its contraction. -/
theorem tensorBranchResidueSum_single_place
    (p h : MonicIrreducible k)
    (q : AdjoinRoot.IrreducibleBranch (h.val.map (algebraMap k (AdjoinRoot p.val))))
    (n : ℕ) (z : K (AdjoinRoot q.val.val) n)
    (x : K (RatFunc (AdjoinRoot p.val)) (n + 1))
    (hx : totalResidue n x = DFinsupp.single q.val z) (h' : MonicIrreducible k) :
    tensorBranchResidueSum p h' n x =
      (DFinsupp.single (β := fun h : MonicIrreducible k => K (AdjoinRoot h.val) n) h
        (polynomialNorm n (AdjoinRoot.tensorSwapBranchEquiv p.val h.val q).val
          (map n (AdjoinRoot.tensorSwapBranchRingEquiv p.val h.val q).toRingHom z))) h' := by
  classical
  unfold tensorBranchResidueSum
  by_cases hh : h' = h
  · subst h'
    rw [DFinsupp.single_eq_same]
    let q0 : {q' // q' ∈ placesAbove (algebraMap k (AdjoinRoot p.val)) h} :=
      ⟨q.val, (mem_placesAbove _ _ _).mpr q.property⟩
    rw [Finset.sum_eq_single q0]
    · have hz : residueAt q.val.val n x = z := by
        simpa only [totalResidue_apply, DFinsupp.single_eq_same] using
          DFunLike.congr_fun hx q.val
      simp only [q0, hz]
    · intro r _ hr
      have hrq : r.val ≠ q.val := by
        intro heq
        apply hr
        exact Subtype.ext heq
      have hz : residueAt r.val.val n x = 0 := by
        simpa only [totalResidue_apply, DFinsupp.single_eq_of_ne hrq] using
          DFunLike.congr_fun hx r.val
      rw [hz, map_zero, map_zero]
    · intro hnot
      exact (hnot (Finset.mem_attach _ q0)).elim
  · rw [DFinsupp.single_eq_of_ne hh]
    apply Finset.sum_eq_zero
    intro r _
    have hrq : r.val ≠ q.val := by
      intro heq
      apply tensorBranch_not_mem_placesAbove p h q h' hh
      exact heq ▸ r.property
    have hz : residueAt r.val.val n x = 0 := by
      simpa only [totalResidue_apply, DFinsupp.single_eq_of_ne hrq] using
        DFunLike.congr_fun hx r.val
    rw [hz, map_zero, map_zero]

open scoped Classical in
/-- The actual rational norm of a single-place lift has only the contracted finite residue. -/
theorem totalResidue_rationalFunctionNorm_single
    (p : MonicIrreducible k) [Normal k (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime) (h : MonicIrreducible k)
    (q : AdjoinRoot.IrreducibleBranch (h.val.map (algebraMap k (AdjoinRoot p.val))))
    (n : ℕ) (z : K (AdjoinRoot q.val.val) n)
    (x : K (RatFunc (AdjoinRoot p.val)) (n + 1))
    (hx : totalResidue n x = DFinsupp.single q.val z) :
    totalResidue n (rationalFunctionNorm (n + 1) p x) =
      DFinsupp.single h
        (polynomialNorm n (AdjoinRoot.tensorSwapBranchEquiv p.val h.val q).val
          (map n (AdjoinRoot.tensorSwapBranchRingEquiv p.val h.val q).toRingHom z)) := by
  classical
  apply DFinsupp.ext
  intro h'
  rw [totalResidue_apply, residueAt_rationalFunctionNorm_prime p hp h' n x]
  exact tensorBranchResidueSum_single_place p h q n z x hx h'

/-- The normal-prime diamond on the actual tensor-matched quotient fields,
proved by a genuine rational lift and the finite and infinite residue squares. -/
theorem polynomialNorm_prime_diamond
    (p : MonicIrreducible k) [Normal k (AdjoinRoot p.val)]
    (hp : p.val.natDegree.Prime) (h : MonicIrreducible k)
    (q : AdjoinRoot.IrreducibleBranch (h.val.map (algebraMap k (AdjoinRoot p.val))))
    (n : ℕ) (z : K (AdjoinRoot q.val.val) n) :
    polynomialNorm n p (polynomialNorm n q.val z) =
      polynomialNorm n h
        (polynomialNorm n (AdjoinRoot.tensorSwapBranchEquiv p.val h.val q).val
          (map n (AdjoinRoot.tensorSwapBranchRingEquiv p.val h.val q).toRingHom z)) := by
  classical
  obtain ⟨x, hx, hnorm⟩ := exists_single_place_rational_norm_lift p hp n q.val z
  have hres := totalResidue_rationalFunctionNorm_single p hp h q n z x hx
  exact hnorm.trans (polynomialNorm_eq_neg_residue_of_lift n h _
    (rationalFunctionNorm (n + 1) p x) hres).symm

end MilnorK.PolynomialNorm
