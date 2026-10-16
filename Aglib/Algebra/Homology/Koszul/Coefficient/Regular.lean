/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Motivic Cohomology contributors
-/
module

public import Aglib.Algebra.Homology.Koszul.Coefficient.Quotient
public import Mathlib.RingTheory.Regular.RegularSequence

/-!
# Regular-sequence hypotheses for quotient coefficients

The literal differential-range quotient is identified with the standard
`QuotSMulTop` module. Consequently mathlib's regular-sequence recursion applies
to the actual quotient coefficient module used by the Koszul comparison.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped Pointwise

namespace ChainComplex.Koszul

variable {R : Type u} [CommRing R]

/-- The literal scalar-image quotient agrees with the standard module quotient. -/
noncomputable def singleQuotientEquivQuotSMulTop (M : ModuleCat R) (a : R) :
    SingleQuotient M a ≃ₗ[R] QuotSMulTop a M :=
  Submodule.quotEquivOfEq _ _ (by
    ext x
    rw [LinearMap.mem_range, Submodule.mem_smul_pointwise_iff_exists]
    simp only [Submodule.mem_top, true_and, LinearMap.lsmul_apply])

/-- The exact regularity recursion in the literal quotient-coefficient convention. -/
theorem coefficient_isWeaklyRegular_cons_iff (M : ModuleCat R) (a : R) (s : List R) :
    RingTheory.Sequence.IsWeaklyRegular M (a :: s) ↔
      IsSMulRegular M a ∧
        RingTheory.Sequence.IsWeaklyRegular ((scalarQuotientFunctor a).obj M) s := by
  rw [RingTheory.Sequence.isWeaklyRegular_cons_iff]
  exact and_congr_right' (singleQuotientEquivQuotSMulTop M a |>.isWeaklyRegular_congr s).symm

end ChainComplex.Koszul
