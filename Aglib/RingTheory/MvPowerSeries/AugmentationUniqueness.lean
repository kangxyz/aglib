/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPowerSeries.TruncIdeal

/-! # Uniqueness of finite-variable augmentation

This is an algebraic statement: finite-variable truncation puts the entire
nonconstant tail in the variable ideal. No topology or continuity is assumed.
-/

@[expose] public section

namespace MvPowerSeries

variable {σ R : Type*} [Finite σ] [CommRing R]

/-- An algebra map killing all finitely many variables is the original augmentation. -/
theorem eq_constantCoeff_of_X (f : MvPowerSeries σ R →ₐ[R] R)
    (hX : ∀ i, f (X i) = 0) : f.toRingHom = constantCoeff := by
  have hk : Ideal.span (Set.range (X : σ → MvPowerSeries σ R)) ≤ RingHom.ker f.toRingHom := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hX i
  ext p
  have ht := sub_truncTotal_mem_span_X_pow 1 p
  rw [pow_one, truncTotal_one_eq_C_constantCoeff, MvPolynomial.coe_C] at ht
  have h : f (p - C (constantCoeff p)) = 0 := hk ht
  rw [map_sub, show f (C (constantCoeff p)) = constantCoeff p from f.commutes _] at h
  exact sub_eq_zero.mp h

end MvPowerSeries
