/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.OriginalBranchResidues
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# The original fraction field of every original branch

Each localized ring maps to the specified original fraction field by its actual
localization lift. This avoids replacing the original extension by a newly
chosen fraction field when stating the residue sum.
-/

@[expose] public noncomputable section

namespace AdicCompletion

variable (S E : Type*) [CommRing S] [IsDedekindDomain S]
  [Field E] [Algebra S E] [IsFractionRing S E] [DecidableEq (Ideal S)]
  {I : Ideal S} (q : IdealBranch I)

/-- The original fraction field receives the actual localization map. -/
@[instance_reducible]
def originalBranchFractionAlgebra : Algebra (Localization.AtPrime q.val) E :=
  (IsLocalization.lift (S := Localization.AtPrime q.val)
    (fun s : q.val.primeCompl => IsUnit.mk0 (algebraMap S E s) (by
      intro h
      have hz : (s : S) = 0 := (IsFractionRing.injective S E) (by simpa using h)
      exact nonZeroDivisors.ne_zero
        (q.val.primeCompl_le_nonZeroDivisors s.property) hz))).toAlgebra

/-- The branch map extends the original domain map literally. -/
theorem originalBranchFractionTower :
    letI := originalBranchFractionAlgebra S E q
    IsScalarTower S (Localization.AtPrime q.val) E := by
  let := originalBranchFractionAlgebra S E q
  apply IsScalarTower.of_algebraMap_eq
  intro s
  exact (IsLocalization.lift_eq _ s).symm

/-- The same original field is the actual fraction field of every branch. -/
theorem originalBranchIsFractionRing :
    letI := originalBranchFractionAlgebra S E q
    IsFractionRing (Localization.AtPrime q.val) E := by
  let := originalBranchFractionAlgebra S E q
  let := originalBranchFractionTower S E q
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.val.primeCompl
    (Localization.AtPrime q.val) E

end AdicCompletion
