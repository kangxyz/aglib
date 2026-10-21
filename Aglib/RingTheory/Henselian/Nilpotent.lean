/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Henselian.Quadratic

/-!
# Henselianity from a nilpotent maximal ideal

Adic Cauchy sequences for a nilpotent ideal are eventually constant. This
constructs actual adic completeness, and hence the native Henselian property,
without assuming Noetherianity or a separate lifting principle.
-/

@[expose] public section

namespace IsAdicComplete

/-- Every module is complete for an ideal with a vanishing power. -/
theorem of_pow_eq_bot {R : Type*} [CommRing R] (I : Ideal R)
    (M : Type*) [AddCommGroup M] [Module R M] {n : ℕ} (hn : I ^ n = ⊥) :
    IsAdicComplete I M where
  haus' x hx := by
    simpa only [hn, Submodule.bot_smul, SModEq.bot] using hx n
  prec' f hf := by
    refine ⟨f n, fun m => ?_⟩
    by_cases hmn : m ≤ n
    · exact hf hmn
    · have he : f n = f m := by
        simpa only [hn, Submodule.bot_smul, SModEq.bot] using
          hf (Nat.le_of_lt (Nat.lt_of_not_ge hmn))
      rw [he]

end IsAdicComplete

namespace HenselianLocalRing

/-- A local ring with nilpotent maximal ideal is Henselian. -/
theorem of_maximalIdeal_pow_eq_bot (R : Type*) [CommRing R] [IsLocalRing R]
    {n : ℕ} (hn : IsLocalRing.maximalIdeal R ^ n = ⊥) : HenselianLocalRing R := by
  let : IsAdicComplete (IsLocalRing.maximalIdeal R) R :=
    IsAdicComplete.of_pow_eq_bot _ _ hn
  exact of_isAdicComplete

end HenselianLocalRing
