/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.MvPowerSeries.FiniteCoefficientExpansion
public import Mathlib.RingTheory.Derivation.Basic

/-!
# Coefficient derivations over the actual expanded base

The original coefficient derivation extends coefficientwise to formal series.
It kills the coefficient-map/expand composite and is linear over that exact base.
-/

@[expose] public noncomputable section

namespace MvPowerSeries

variable {E k : Type*} [Field E] [Field k] [Algebra E k]

/-- Apply an actual coefficient-field derivation to every coefficient. -/
def coefficientLinearMap (δ : Derivation E k k) :
    MvPowerSeries (Fin 2) k →ₗ[E] MvPowerSeries (Fin 2) k where
  toFun f := fun n => δ (coeff n f)
  map_add' f g := by
    funext n
    exact map_add δ (coeff n f) (coeff n g)
  map_smul' a f := by
    funext n
    exact δ.map_smul a (coeff n f)

@[simp]
theorem coeff_coefficientLinearMap (δ : Derivation E k k)
    (f : MvPowerSeries (Fin 2) k) (n : Fin 2 →₀ ℕ) :
    coeff n (coefficientLinearMap δ f) = δ (coeff n f) := rfl

/-- The finite Cauchy sum proves the Leibniz rule coefficient by coefficient. -/
theorem coefficientLinearMap_leibniz (δ : Derivation E k k)
    (f g : MvPowerSeries (Fin 2) k) :
    coefficientLinearMap δ (f * g) =
      f • coefficientLinearMap δ g + g • coefficientLinearMap δ f := by
  classical
  apply MvPowerSeries.ext
  intro n
  change δ (coeff n (f * g)) =
    coeff n (f * coefficientLinearMap δ g + g * coefficientLinearMap δ f)
  rw [mul_comm g (coefficientLinearMap δ f), coeff_mul, map_sum,
    map_add, coeff_mul, coeff_mul, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  change δ (coeff a.1 f * coeff a.2 g) =
    coeff a.1 f * δ (coeff a.2 g) + δ (coeff a.1 f) * coeff a.2 g
  simpa only [smul_eq_mul, mul_comm] using δ.leibniz (coeff a.1 f) (coeff a.2 g)

/-- The coefficientwise construction is an ordinary algebraic derivation. -/
def coefficientDerivation (δ : Derivation E k k) :
    Derivation E (MvPowerSeries (Fin 2) k) (MvPowerSeries (Fin 2) k) :=
  Derivation.mk' (coefficientLinearMap δ) (coefficientLinearMap_leibniz δ)

@[simp]
theorem coeff_coefficientDerivation (δ : Derivation E k k)
    (f : MvPowerSeries (Fin 2) k) (n : Fin 2 →₀ ℕ) :
    coeff n (coefficientDerivation δ f) = δ (coeff n f) := rfl

@[simp]
theorem coefficientDerivation_C (δ : Derivation E k k) (a : k) :
    coefficientDerivation δ (C a) = C (δ a) := by
  classical
  apply MvPowerSeries.ext
  intro n
  rw [coeff_coefficientDerivation]
  by_cases hn : n = 0 <;> simp [coeff_C, hn]

@[simp]
theorem coefficientDerivation_X (δ : Derivation E k k) (i : Fin 2) :
    coefficientDerivation δ (X i) = 0 := by
  classical
  apply MvPowerSeries.ext
  intro n
  rw [coeff_coefficientDerivation, coeff_zero]
  by_cases hn : n = Finsupp.single i 1 <;> simp [coeff_X, hn]

/-- Every series in the original expanded coefficient subring is killed. -/
theorem coefficientDerivation_scalarMap (δ : Derivation E k k)
    (q : ℕ) (hq : q ≠ 0) (f : MvPowerSeries (Fin 2) E) :
    coefficientDerivation δ (FiniteCoefficientExpansion.scalarMap q hq f) = 0 := by
  apply MvPowerSeries.ext
  intro n
  rw [coeff_coefficientDerivation, coeff_zero]
  by_cases hd : ∀ i, q ∣ n i
  · let m : Fin 2 →₀ ℕ := n.mapRange (fun a => a / q) (Nat.zero_div q)
    have hn : n = q • m := by
      ext i
      simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.mapRange_apply, m]
      exact (Nat.mul_div_cancel' (hd i)).symm
    rw [hn, FiniteCoefficientExpansion.scalarMap_apply, coeff_expand_smul,
      coeff_map, δ.map_algebraMap]
  · push Not at hd
    obtain ⟨i, hi⟩ := hd
    rw [FiniteCoefficientExpansion.scalarMap_apply, coeff_expand_of_not_dvd q hq _ hi,
      map_zero]

/-- The same map is linear over the actual expanded series base because it kills that base. -/
def coefficientDerivationOverExpansion (δ : Derivation E k k) (q : ℕ) (hq : q ≠ 0) :
    letI := FiniteCoefficientExpansion.scalarAlgebra (k₀ := E) (k := k) q hq
    Derivation (MvPowerSeries (Fin 2) E) (MvPowerSeries (Fin 2) k)
      (MvPowerSeries (Fin 2) k) := by
  letI := FiniteCoefficientExpansion.scalarAlgebra (k₀ := E) (k := k) q hq
  let D := coefficientDerivation δ
  refine
    { toFun := D
      map_add' := map_add D
      map_smul' := ?_
      map_one_eq_zero' := D.map_one_eq_zero
      leibniz' := D.leibniz }
  intro a f
  change D (FiniteCoefficientExpansion.scalarMap q hq a * f) =
    FiniteCoefficientExpansion.scalarMap q hq a * D f
  rw [D.leibniz, show D (FiniteCoefficientExpansion.scalarMap q hq a) = 0 from
    coefficientDerivation_scalarMap δ q hq a]
  simp only [smul_eq_mul, mul_zero, add_zero]

@[simp]
theorem coeff_coefficientDerivationOverExpansion (δ : Derivation E k k)
    (q : ℕ) (hq : q ≠ 0) (f : MvPowerSeries (Fin 2) k) (n : Fin 2 →₀ ℕ) :
    letI := FiniteCoefficientExpansion.scalarAlgebra (k₀ := E) (k := k) q hq
    coeff n (coefficientDerivationOverExpansion δ q hq f) = δ (coeff n f) := rfl

end MvPowerSeries
