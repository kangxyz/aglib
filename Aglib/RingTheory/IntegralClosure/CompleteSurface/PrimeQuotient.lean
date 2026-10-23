/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.CompleteSurface
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.Tactic.NormNum

/-!
# Finite normalization of prime quotients of a complete normal local surface

Every prime quotient of a complete Noetherian normal local domain of
dimension at most two has finite literal normalization in every finite
extension of its fraction field. At the zero prime, normality of the
quotient permits the complete-surface theorem. At every nonzero prime, a
nonzero kernel element gives dimension at most one, and the complete-curve
theorem applies without requiring the quotient to be normal.

The fraction field, extension field, coefficient maps, and integral closure
remain the supplied actual ones. No separability assumption is imposed.
This is the prime-quotient bridge; it does not assert finite-type stability.
-/

@[expose] public noncomputable section

open scoped nonZeroDivisors

namespace integralClosure

variable (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R]
  [IsIntegrallyClosed R] [IsLocalRing R] [Ring.KrullDimLE 2 R]
  [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
  (p : Ideal R) [p.IsPrime]
  (K L : Type*) [Field K] [Algebra (R ⧸ p) K] [IsFractionRing (R ⧸ p) K]
  [Field L] [Algebra K L] [Algebra (R ⧸ p) L] [IsScalarTower (R ⧸ p) K L]
  [FiniteDimensional K L]

include K

/-- Every actual prime quotient of a complete Noetherian normal local
domain of dimension at most two has finite normalization in any finite
extension of its supplied fraction field. The prime quotient need not be
normal, and the field extension need not be separable. -/
theorem finite_primeQuotient_of_complete_local_normal_dimLE_two :
    Module.Finite (R ⧸ p) (integralClosure (R ⧸ p) L) := by
  let : IsNoetherianRing (R ⧸ p) := isNoetherianRing_of_surjective R (R ⧸ p)
    (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  let : IsLocalRing (R ⧸ p) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  let : IsAdicComplete (IsLocalRing.maximalIdeal (R ⧸ p)) (R ⧸ p) := by
    have h := IsAdicComplete.map_algebraMap_of_finite R (IsLocalRing.maximalIdeal R) (R ⧸ p)
    rwa [IsLocalRing.map_maximalIdeal_of_surjective
      (algebraMap R (R ⧸ p)) Ideal.Quotient.mk_surjective] at h
  by_cases hp : p = ⊥
  · let : IsIntegrallyClosed (R ⧸ p) := by
      subst p
      exact IsIntegrallyClosed.of_equiv (RingEquiv.quotientBot R).symm
    let : Ring.KrullDimLE 2 (R ⧸ p) := Ring.krullDimLE_iff.mpr
      ((ringKrullDim_quotient_le p).trans
        (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 2 R)))
    exact finite_of_complete_local_normal_dimLE_two (R ⧸ p) K L
  · obtain ⟨x, hxp, hx⟩ := p.ne_bot_iff.mp hp
    let : Ring.KrullDimLE 1 (R ⧸ p) := by
      apply Ring.krullDimLE_iff.mpr
      apply ENat.WithBot.add_le_add_one_right_iff.mp
      have hdim := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk p)
        Ideal.Quotient.mk_surjective (mem_nonZeroDivisors_iff_ne_zero.mpr hx)
        (Ideal.Quotient.eq_zero_iff_mem.mpr hxp)
      convert hdim.trans
        (Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 2 R)) using 1
      norm_num
    exact finite_of_complete_local_dimLE_one (R ⧸ p) K L

end integralClosure
