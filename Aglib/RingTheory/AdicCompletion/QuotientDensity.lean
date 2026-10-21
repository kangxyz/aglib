/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.Congruence
public import Mathlib.RingTheory.AdicCompletion.LocalRing

/-! # Actual quotient density of a ring in its adic completion -/

@[expose] public section

namespace AdicCompletion

variable {R : Type*} [CommRing R]

/-- Every completion element modulo an extended ideal power has an original
coefficient representative. This includes order zero. -/
theorem quotient_algebraMap_surjective (I : Ideal R) (hI : I.FG) (n : ℕ) :
    Function.Surjective
      ((Ideal.Quotient.mk ((I ^ n).map (algebraMap R (AdicCompletion I R)))).comp
        (algebraMap R (AdicCompletion I R))) := by
  intro q
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective q
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (evalₐ I n x)
  refine ⟨r, ?_⟩
  change Ideal.Quotient.mk _ (algebraMap R (AdicCompletion I R) r) =
    Ideal.Quotient.mk _ x
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  apply (evalₐ_eq_iff_sub_mem I hI n _ _).mp
  rw [(evalₐ I n).commutes]
  exact hr

/-- The actual completion map of a Noetherian local ring surjects onto every
quotient by a power of the completion's own maximal ideal. -/
theorem quotient_maximalIdeal_pow_algebraMap_surjective
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (n : ℕ) :
    Function.Surjective
      ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
        (AdicCompletion (IsLocalRing.maximalIdeal R) R) ^ n)).comp
        (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R))) := by
  rw [maximalIdeal_eq_map, ← Ideal.map_pow]
  exact quotient_algebraMap_surjective _ (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing n

end AdicCompletion
