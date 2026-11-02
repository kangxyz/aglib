/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.UnitRoots
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
public import Mathlib.RingTheory.Localization.FractionRing

/-! # Primitive roots from the original Henselian residue field

Lift a prescribed primitive residue root using the actual unit-root lifting
map. The order is retained by reduction. Injectivity of the original fraction
map then transports the primitive root without choosing a new field.
-/

@[expose] public noncomputable section

namespace HenselianLocalRing

open IsLocalRing

variable (R : Type*) [CommRing R] [HenselianLocalRing R]

/-- A prescribed primitive residue root lifts to a primitive root with exactly
that residue, for a positive invertible order. No domain condition is needed. -/
theorem exists_primitiveRoot_with_residue
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R))
    (c : ResidueField R) (hc : IsPrimitiveRoot c n) :
    ∃ ζ : R, residue R ζ = c ∧ IsPrimitiveRoot ζ n := by
  obtain ⟨v, hv, hvpow⟩ := exists_unit_root_with_residue n hn hunit (1 : Rˣ) c
    (by simpa only [Units.val_one, map_one] using hc.pow_eq_one)
  refine ⟨v, hv, ?_⟩
  constructor
  · exact congrArg (fun w : Rˣ => (w : R)) hvpow
  · intro m hm
    apply hc.dvd_of_pow_eq_one m
    rw [← hv, ← map_pow, hm, map_one]

/-- A strictly Henselian local ring contains primitive roots of every positive
invertible order, obtained from the original residue field. -/
theorem exists_primitiveRoot_of_isSepClosed_residue
    [IsSepClosed (ResidueField R)] (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R)) :
    ∃ ζ : R, IsPrimitiveRoot ζ n := by
  let : NeZero (n : ResidueField R) := ⟨by
    simpa only [map_natCast] using (hunit.map (residue R)).ne_zero⟩
  obtain ⟨c, hc⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (ResidueField R) n
  obtain ⟨ζ, _, hζ⟩ := exists_primitiveRoot_with_residue R n hn hunit c hc
  exact ⟨ζ, hζ⟩

/-- The original fraction field contains the primitive roots lifted in the
strictly Henselian ring through its injective fraction map. -/
theorem primitiveRoots_fraction_nonempty [IsSepClosed (ResidueField R)]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : R)) :
    (primitiveRoots n K).Nonempty := by
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_isSepClosed_residue R n hn hunit
  exact ⟨algebraMap R K ζ, (mem_primitiveRoots hn).mpr
    (hζ.map_of_injective (IsFractionRing.injective R K))⟩

end HenselianLocalRing
