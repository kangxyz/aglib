/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Ideal.SquareZeroUnits
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition

/-!
# Square-zero kernels of successive ideal-power quotients

The kernel is the image of the original ideal power, without a flat tensor
identification. The original `factorPowSucc` therefore gives the actual
square-zero unit sequence used by the formal line-bundle lifting tower.
-/

@[expose] public section

namespace Ideal.Quotient

variable {R : Type*} [CommRing R] (I : Ideal R)

/-- The kernel of the original transition is the image of the lower ideal power. -/
theorem ker_factorPow_eq_map {m n : ℕ} (h : n ≤ m) :
    RingHom.ker (factorPow I h) = (I ^ n).map (mk (I ^ m)) :=
  factor_ker (Ideal.pow_le_pow_right h)

/-- Every successor kernel above the closed-fibre level is square zero. -/
theorem ker_factorPowSucc_sq (n : ℕ) :
    RingHom.ker (factorPowSucc I (n + 1)) ^ 2 = ⊥ := by
  rw [ker_factorPow_eq_map, ← Ideal.map_pow, ← pow_mul]
  apply Ideal.map_mk_eq_bot_of_le
  exact Ideal.pow_le_pow_right (by omega)

/-- Units lift through the original positive-level transition. -/
theorem units_factorPowSucc_surjective (n : ℕ) :
    Function.Surjective (Units.map
      (factorPowSucc I (n + 1) : R ⧸ I ^ (n + 1 + 1) →* R ⧸ I ^ (n + 1))) := by
  intro u
  obtain ⟨x, hx⟩ := factor_surjective
    (Ideal.pow_le_pow_right (Nat.le_succ (n + 1))) (u : R ⧸ I ^ (n + 1))
  have hunit : IsUnit x := factorPowSucc.isUnit_of_isUnit_image (by omega)
    (hx.symm ▸ u.isUnit)
  refine ⟨hunit.unit, ?_⟩
  apply Units.ext
  change factorPowSucc I (n + 1) (hunit.unit : R ⧸ I ^ (n + 1 + 1)) = _
  rw [hunit.unit_spec]
  exact hx

/-- The actual successor unit kernel, with its canonical one-plus coordinates. -/
noncomputable def factorPowSuccUnitsKerEquiv (n : ℕ) :
    Multiplicative (RingHom.ker (factorPowSucc I (n + 1))) ≃*
      (Units.map (factorPowSucc I (n + 1) : R ⧸ I ^ (n + 1 + 1) →* R ⧸ I ^ (n + 1))).ker :=
  (factorPowSucc I (n + 1)).oneAddUnitsKerEquiv (ker_factorPowSucc_sq I n)

@[simp]
theorem coe_factorPowSuccUnitsKerEquiv (n : ℕ)
    (x : Multiplicative (RingHom.ker (factorPowSucc I (n + 1)))) :
    ((factorPowSuccUnitsKerEquiv I n x : (R ⧸ I ^ (n + 1 + 1))ˣ) :
      R ⧸ I ^ (n + 1 + 1)) = 1 + x.toAdd := rfl

end Ideal.Quotient
