/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing

/-!
# Ordinary field norms and normalized DVR orders

For a finite integral-closure extension of discrete valuation rings, the
ordinary field norm multiplies the normalized integer order by the actual
residue-field degree. The proof uses the relative norm of principal ideals,
not a supplied compatibility axiom. The perfect base fraction field assumption
is explicit because the pinned ideal-norm theorem requires it.
-/

@[expose] public noncomputable section

open scoped WithZero
open IsLocalRing

namespace IsDiscreteValuationRing.NormValuation

section Order

variable (R K : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The normalized integer order of a nonzero fraction-field element, defined
using the native maximal-ideal valuation. -/
def order (a : Kˣ) : ℤ :=
  -WithZero.log ((IsDiscreteValuationRing.maximalIdeal R).valuation K (a : K))

@[simp] theorem order_mul (a b : Kˣ) : order R K (a * b) = order R K a + order R K b := by
  unfold order
  rw [Units.val_mul, map_mul, WithZero.log_mul
    ((map_ne_zero _).mpr a.ne_zero) ((map_ne_zero _).mpr b.ne_zero), neg_add]

@[simp] theorem order_one : order R K 1 = 0 := by simp [order]

/-- The integer order, viewed as an additive homomorphism on multiplicative units. -/
def orderHom : Additive Kˣ →+ ℤ where
  toFun a := order R K a.toMul
  map_zero' := order_one R K
  map_add' a b := order_mul R K a.toMul b.toMul

@[simp] theorem order_zpow (a : Kˣ) (n : ℤ) : order R K (a ^ n) = n * order R K a := by
  exact (orderHom R K).map_zsmul n (Additive.ofMul a)

@[simp] theorem order_inv (a : Kˣ) : order R K a⁻¹ = -order R K a := by
  simpa using order_zpow R K a (-1)

theorem order_ringUnit (u : Rˣ) :
    order R K (Units.map (algebraMap R K).toMonoidHom u) = 0 := by
  have hv : (IsDiscreteValuationRing.maximalIdeal R).valuation K
      (algebraMap R K (u : R)) = 1 := by
    simp [IsDiscreteValuationRing.maximalIdeal]
  change -WithZero.log ((IsDiscreteValuationRing.maximalIdeal R).valuation K
    (algebraMap R K (u : R))) = 0
  rw [hv, WithZero.log_one, neg_zero]

/-- An actual irreducible of the DVR as a fraction-field unit. -/
def uniformizerUnit {π : R} (hπ : Irreducible π) : Kˣ :=
  Units.mk0 (algebraMap R K π) (by simpa using hπ.ne_zero)

@[simp] theorem order_uniformizer {π : R} (hπ : Irreducible π) :
    order R K (uniformizerUnit R K hπ) = 1 := by
  unfold order uniformizerUnit
  rw [Units.val_mk0, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
    (IsDiscreteValuationRing.maximalIdeal R).intValuation_singleton hπ.ne_zero
      hπ.maximalIdeal_eq, WithZero.log_exp]
  rfl

end Order

/-- A uniformizer norm generates precisely the residue-degree power of the
base maximal ideal. This uses the actual integral and relative ideal norms. -/
theorem span_intNorm_uniformizer
    (R B : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    [Algebra R B] [Module.Finite R B] [Module.IsTorsionFree R B]
    [PerfectField (FractionRing R)] {π : B} (hπ : Irreducible π) :
    Ideal.span ({Algebra.intNorm R B π} : Set R) =
      IsLocalRing.maximalIdeal R ^ (IsLocalRing.maximalIdeal B).inertiaDeg R := by
  rw [← Ideal.relNorm_singleton, ← hπ.maximalIdeal_eq]
  exact Ideal.relNorm_eq_pow_of_isMaximal (IsLocalRing.maximalIdeal B) (IsLocalRing.maximalIdeal R)

section Norm

variable (R B K L : Type*)
  [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra R B] [Module.Finite R B] [Module.IsTorsionFree R B]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field L] [Algebra K L] [Algebra R L] [IsScalarTower R K L]
  [Algebra B L] [IsScalarTower R B L]
  [IsIntegralClosure B R L] [FiniteDimensional K L]

/-- The ordinary norm of a ring unit is a ring unit in the base DVR. -/
theorem norm_ringUnit (u : Bˣ) :
    Units.map (Algebra.norm K) (Units.map (algebraMap B L).toMonoidHom u) =
      Units.map (algebraMap R K).toMonoidHom (Units.map (Algebra.intNorm R B) u) := by
  apply Units.ext
  exact (Algebra.algebraMap_intNorm (K := K) (L := L) (u : B)).symm

theorem order_norm_ringUnit (u : Bˣ) :
    order R K (Units.map (Algebra.norm K) (Units.map (algebraMap B L).toMonoidHom u)) = 0 := by
  rw [norm_ringUnit R B K L, order_ringUnit]

variable [IsFractionRing B L] [PerfectField K]

/-- The ordinary norm of a uniformizer has order the actual inertia degree. -/
theorem order_norm_uniformizer {π : B} (hπ : Irreducible π) :
    order R K (Units.map (Algebra.norm K) (uniformizerUnit B L hπ)) =
      (IsLocalRing.maximalIdeal B).inertiaDeg R := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  let : PerfectField (FractionRing R) :=
    PerfectField.of_ringEquiv (FractionRing.algEquiv R K).symm.toRingEquiv
  have hs := span_intNorm_uniformizer R B hπ
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow] at hs
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hs
  have hv := congrArg (fun x : R =>
    (IsDiscreteValuationRing.maximalIdeal R).valuation K (algebraMap R K x)) hu
  have hvu : (IsDiscreteValuationRing.maximalIdeal R).valuation K
      (algebraMap R K (u : R)) = 1 := by
    simp [IsDiscreteValuationRing.maximalIdeal]
  have hvϖ : (IsDiscreteValuationRing.maximalIdeal R).valuation K
      (algebraMap R K ϖ) = WithZero.exp (-1 : ℤ) := by
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    exact (IsDiscreteValuationRing.maximalIdeal R).intValuation_singleton hϖ.ne_zero
      hϖ.maximalIdeal_eq
  simp only [map_mul, map_pow, hvu, mul_one, hvϖ] at hv
  change -WithZero.log ((IsDiscreteValuationRing.maximalIdeal R).valuation K
    (Algebra.norm K (algebraMap B L π))) = _
  rw [← Algebra.algebraMap_intNorm (A := R) (K := K) (L := L), hv,
    ← WithZero.exp_nsmul, WithZero.log_exp]
  simp

/-- The normalized integer order of the ordinary field norm is multiplied by
the actual residue-field degree. The theorem applies to arbitrary field units,
including negative orders, and assumes no norm-valuation compatibility. -/
theorem order_norm (h : Lˣ) :
    order R K (Units.map (Algebra.norm K) h) =
      (Module.finrank (ResidueField R) (ResidueField B) : ℤ) * order B L h := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
    hπ h.ne_zero
  have hh : h = Units.map (algebraMap B L).toMonoidHom u * uniformizerUnit B L hπ ^ n := by
    apply Units.ext
    simpa [uniformizerUnit, Units.smul_def, Algebra.smul_def] using hu
  rw [hh, map_mul, map_zpow, order_mul, order_zpow, order_norm_ringUnit R B K L,
    order_norm_uniformizer R B K L hπ, order_mul, order_ringUnit, order_zpow,
    order_uniformizer, zero_add, zero_add, mul_one]
  rw [Ideal.inertiaDeg_eq_of_isMaximal (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal B)]
  exact mul_comm _ _

end Norm

end IsDiscreteValuationRing.NormValuation
