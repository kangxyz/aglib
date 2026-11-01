/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Smooth.GenericConnectedness
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Localization.BaseChange

/-! # Normality descent from the actual generic fibre of a smooth algebra -/

@[expose] public section

open scoped TensorProduct nonZeroDivisors

namespace Algebra.Smooth

universe u

variable (R K S : Type u) [CommRing R] [IsDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [CommRing S] [Algebra R S] [Algebra.Smooth R S]

/-- The actual generic fibre of a smooth domain algebra is a domain. -/
theorem generic_isDomain [IsDomain S] : IsDomain (S ⊗[R] K) := by
  apply IsLocalization.isDomain_of_le_nonZeroDivisors
    (S ⊗[R] K) (M := Algebra.algebraMapSubmonoid S R⁰)
  exact map_le_nonZeroDivisors_of_injective (algebraMap R S)
    (FaithfulSMul.algebraMap_injective R S) le_rfl

omit [IsDomain R] in
/-- Smooth base change of a normal domain contains every integral element
of its actual generic fibre. -/
theorem isIntegrallyClosedIn_generic [IsIntegrallyClosed R] :
    IsIntegrallyClosedIn S (S ⊗[R] K) := by
  apply isIntegrallyClosedIn_iff.mpr
  exact ⟨generic_algebraMap_injective R K S,
    fun hx => integral_generic_has_preimage R K S _ hx⟩

/-- Normality of the actual generic fibre descends to the original smooth
algebra over a normal domain. This is a lower descent lemma; generic-fibre
normality is discharged by the smooth-field supplier in the scheme bridge. -/
theorem isIntegrallyClosed_of_generic [IsIntegrallyClosed R] [IsDomain S]
    [IsIntegrallyClosed (S ⊗[R] K)] : IsIntegrallyClosed S := by
  let : IsDomain (S ⊗[R] K) := generic_isDomain R K S
  let : IsIntegrallyClosedIn S (S ⊗[R] K) := isIntegrallyClosedIn_generic R K S
  let : FaithfulSMul S (S ⊗[R] K) :=
    IsIntegralClosure.faithfulSMul S S (S ⊗[R] K)
  exact IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn
    (R := S) (S := S ⊗[R] K)

end Algebra.Smooth
