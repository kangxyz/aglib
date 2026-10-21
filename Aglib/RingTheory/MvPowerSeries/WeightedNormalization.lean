/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Data.Finsupp.LexWeight
public import Aglib.RingTheory.MvPowerSeries.WeightedSpecialization
public import Mathlib.RingTheory.MvPowerSeries.LexOrder

/-!
# Nonvanishing weighted specialization

Every nonzero formal power series in a positive finite number of variables
has a nonzero specialization to positive powers of one variable, with the
last original variable assigned exponent one. This holds over arbitrary
commutative rings. It isolates the lexicographically first nonzero coefficient
rather than making a generic linear change over an infinite field.
-/

@[expose] public section

namespace MvPowerSeries

variable {R : Type*} [CommRing R]

/-- Nonvanishing weighted specialization, without hypotheses on the residue field. -/
theorem exists_pos_weight_subst_ne_zero (n : ℕ)
    (f : MvPowerSeries (Fin (n + 1)) R) (hf : f ≠ 0) :
    ∃ w : Fin (n + 1) → ℕ,
      (∀ i, 0 < w i) ∧ w (Fin.last n) = 1 ∧
      subst (fun i ↦ (X () : MvPowerSeries Unit R) ^ w i) f ≠ 0 := by
  classical
  obtain ⟨a, ha⟩ := exists_finsupp_eq_lexOrder_of_ne_zero hf
  obtain ⟨w, hw, hlast, hlex⟩ := Finsupp.exists_pos_weight_lt_of_lex_lt n a
  refine ⟨w, hw, hlast, ?_⟩
  have hisolate : ∀ d, d ≠ a → coeff d f ≠ 0 →
      Finsupp.weight w a < Finsupp.weight w d := by
    intro d hd hdf
    apply hlex d
    have hle : toLex a ≤ toLex d := by
      apply WithTop.coe_le_coe.mp
      rw [← ha]
      exact lexOrder_le_of_coeff_ne_zero hdf
    have hne : toLex a ≠ toLex d := by
      intro h
      exact hd (congrArg ofLex h).symm
    exact lt_of_le_of_ne hle hne
  have hc := coeff_subst_X_pow_weight_eq_of_isolated () w hw f a hisolate
  intro hz
  rw [hz, map_zero] at hc
  exact coeff_ne_zero_of_lexOrder ha.symm hc.symm

end MvPowerSeries
