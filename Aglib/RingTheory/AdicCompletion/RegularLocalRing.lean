/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.NoetherianRing
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regularity and the actual maximal-adic completion

For a Noetherian local ring, the native completion map is flat and extends
the original maximal ideal to the completion's maximal ideal. The height
formula therefore preserves local Krull dimension. The native equality of
maximal-ideal generator counts then identifies regularity of the two rings.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace AdicCompletion

variable (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- The actual maximal-adic completion preserves local Krull dimension.
Flatness is the native instance for this completion, rather than a premise. -/
theorem ringKrullDim_maximalIdeal_eq :
    ringKrullDim (AdicCompletion (maximalIdeal R) R) = ringKrullDim R := by
  let : IsNoetherianRing (AdicCompletion (maximalIdeal R) R) :=
    AdicCompletion.isNoetherianRing R (maximalIdeal R)
  have hheight := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (maximalIdeal R) (maximalIdeal (AdicCompletion (maximalIdeal R) R))
  rw [← AdicCompletion.maximalIdeal_eq_map, Ideal.map_quotient_self, Ideal.height_bot,
    add_zero] at hheight
  simpa using congrArg (fun n : ℕ∞ ↦ (n : WithBot ℕ∞)) hheight

/-- A Noetherian local ring is regular exactly when its actual maximal-adic
completion is regular. Both native ring objects and maximal ideals are retained. -/
theorem isRegularLocalRing_iff_maximalCompletion :
    IsRegularLocalRing R ↔ IsRegularLocalRing (AdicCompletion (maximalIdeal R) R) := by
  let : IsNoetherianRing (AdicCompletion (maximalIdeal R) R) :=
    AdicCompletion.isNoetherianRing R (maximalIdeal R)
  rw [isRegularLocalRing_iff R,
    isRegularLocalRing_iff (AdicCompletion (maximalIdeal R) R),
    AdicCompletion.spanFinrank_maximalIdeal_eq, ringKrullDim_maximalIdeal_eq R]

end AdicCompletion
