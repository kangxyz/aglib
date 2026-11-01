/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPowerSeries.TruncIdeal

/-! # The original variable ideal is the augmentation kernel -/

@[expose] public section

namespace MvPowerSeries

variable {σ R : Type*} [Finite σ] [CommRing R]

/-- For finitely many variables, the actual variable ideal is the kernel of
constant coefficient. No completeness of the coefficient ring is required. -/
theorem span_X_eq_ker_constantCoeff :
    Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) = RingHom.ker constantCoeff := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact constantCoeff_X i
  · intro f hf
    have h := sub_truncTotal_mem_span_X_pow 1 f
    have hf' : constantCoeff f = 0 := hf
    simpa only [pow_one, truncTotal_one_eq_C_constantCoeff, hf', map_zero,
      MvPolynomial.coe_zero, sub_zero] using h

end MvPowerSeries
