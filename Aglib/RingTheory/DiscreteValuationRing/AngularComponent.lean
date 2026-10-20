/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Group.Units.Map
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.LinearCombination
public import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
public import Mathlib.RingTheory.DedekindDomain.SelmerGroup
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-!
# Integer order and angular components of DVR fractions

The fraction valuation is the actual maximal-ideal valuation. Removing its
integer uniformizer power gives a genuine unit of the original DVR. The
construction preserves arbitrary ring and fraction-field universes. The
residue identities for `x + y = 1` concern ordinary units; no Milnor group or
tame map is imported or constructed here.
-/

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/RingTheory/DiscreteValuationRing/AngularComponent.lean` at
R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`720c3fac11b9abbab6fda570c3a780cff6f32da3009e05e875f22fc8f2206199`.
-/

@[expose] public section

namespace IsDiscreteValuationRing

open IsLocalRing
open scoped WithZero

universe u v

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The canonical multiplicative valuation on the fraction field of the DVR. -/
noncomputable abbrev fractionValuation : Valuation K ℤᵐ⁰ :=
  (IsDiscreteValuationRing.maximalIdeal R).valuation K

/-- The integer order, positive on a uniformizer. -/
noncomputable def fractionOrder (x : Kˣ) : ℤ :=
  -((IsDiscreteValuationRing.maximalIdeal R).valuationOfNeZero x).toAdd

@[simp] theorem fractionOrder_one : fractionOrder R K (1 : Kˣ) = 0 := by
  simp [fractionOrder]

@[simp] theorem fractionOrder_mul (x y : Kˣ) :
    fractionOrder R K (x * y) = fractionOrder R K x + fractionOrder R K y := by
  simp [fractionOrder, add_comm]

@[simp] theorem fractionOrder_inv (x : Kˣ) : fractionOrder R K x⁻¹ = -fractionOrder R K x := by
  simp [fractionOrder]

@[simp] theorem fractionOrder_zpow (x : Kˣ) (n : ℤ) :
    fractionOrder R K (x ^ n) = n * fractionOrder R K x := by
  simp [fractionOrder, mul_neg]

/-- Comparison of the integer order with mathlib's canonical valuation. -/
theorem fractionValuation_eq (x : Kˣ) :
    fractionValuation R K (x : K) = WithZero.exp (-fractionOrder R K x) := by
  simp only [fractionOrder, neg_neg, WithZero.exp_eq_coe_ofAdd]
  exact ((IsDiscreteValuationRing.maximalIdeal R).valuationOfNeZero_eq x).symm

/-- This order is minus the logarithm of the same actual maximal-ideal valuation. -/
theorem fractionOrder_eq_neg_log (x : Kˣ) :
    fractionOrder R K x = -WithZero.log (fractionValuation R K (x : K)) := by
  rw [fractionValuation_eq, WithZero.log_exp, neg_neg]

/-- The canonical map on units into the fraction field. -/
def fractionUnits : Rˣ →* Kˣ := Units.map (algebraMap R K).toMonoidHom

/-- Units of the DVR have order zero in its fraction field. -/
@[simp] theorem fractionOrder_fractionUnits (u : Rˣ) :
    fractionOrder R K (fractionUnits R K u) = 0 := by
  simp [fractionOrder, fractionUnits]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The map of DVR units into the fraction field is injective. -/
theorem fractionUnits_injective : Function.Injective (fractionUnits R K) := by
  intro a b h
  apply Units.ext
  apply IsFractionRing.injective R K
  exact congrArg Units.val h

variable {R K}

/-- A chosen actual uniformizer, viewed as a unit in the fraction field. -/
noncomputable def uniformizerUnit {π : R} (hπ : Irreducible π) : Kˣ :=
  Units.mk0 (algebraMap R K π) (by
    intro h
    exact hπ.ne_zero ((IsFractionRing.injective R K) (by simpa using h)))

@[simp] theorem fractionValuation_uniformizer {π : R} (hπ : Irreducible π) :
    fractionValuation R K (uniformizerUnit (K := K) hπ : K) = WithZero.exp (-1 : ℤ) := by
  change (IsDiscreteValuationRing.maximalIdeal R).valuation K (algebraMap R K π) = _
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
  exact (IsDiscreteValuationRing.maximalIdeal R).intValuation_singleton
    hπ.ne_zero hπ.maximalIdeal_eq

@[simp] theorem fractionOrder_uniformizer {π : R} (hπ : Irreducible π) :
    fractionOrder R K (uniformizerUnit (K := K) hπ) = 1 := by
  have h := fractionValuation_uniformizer (K := K) hπ
  rw [fractionValuation_eq, WithZero.exp_inj] at h
  omega

/-- Removing the exact uniformizer power from an element of the fraction field. -/
noncomputable def normalizedUnit {π : R} (hπ : Irreducible π) (x : Kˣ) : Kˣ :=
  x * uniformizerUnit (K := K) hπ ^ (-fractionOrder R K x)

@[simp] theorem fractionOrder_normalizedUnit {π : R} (hπ : Irreducible π) (x : Kˣ) :
    fractionOrder R K (normalizedUnit hπ x) = 0 := by
  simp [normalizedUnit]

/-- An element of order zero is the image of an actual DVR unit. -/
theorem exists_fractionUnit_of_fractionOrder_zero (x : Kˣ) (hx : fractionOrder R K x = 0) :
    ∃ u : Rˣ, fractionUnits R K u = x := by
  have hv : fractionValuation R K (x : K) = 1 := by rw [fractionValuation_eq, hx]; simp
  have hm : (x : K) ∈ MonoidHom.mker (fractionValuation R K) := hv
  rw [IsDiscreteValuationRing.mker_valuation_eq_isUnitSubmonoid] at hm
  rcases hm with ⟨r, hr, heq⟩
  refine ⟨hr.unit, ?_⟩
  apply Units.ext
  simpa [fractionUnits, hr.unit_spec] using heq

/-- The normalized coefficient is a genuine unit of the original DVR. -/
noncomputable def angularComponent {π : R} (hπ : Irreducible π) (x : Kˣ) : Rˣ :=
  (exists_fractionUnit_of_fractionOrder_zero (normalizedUnit hπ x)
    (fractionOrder_normalizedUnit hπ x)).choose

@[simp] theorem fractionUnits_angularComponent {π : R} (hπ : Irreducible π) (x : Kˣ) :
    fractionUnits R K (angularComponent hπ x) = normalizedUnit hπ x :=
  (exists_fractionUnit_of_fractionOrder_zero (normalizedUnit hπ x)
    (fractionOrder_normalizedUnit hπ x)).choose_spec

/-- Multiplicativity of the normalized DVR-unit component. -/
theorem angularComponent_mul {π : R} (hπ : Irreducible π) (x y : Kˣ) :
    angularComponent hπ (x * y) = angularComponent hπ x * angularComponent hπ y := by
  apply fractionUnits_injective R K
  simp only [map_mul, fractionUnits_angularComponent, normalizedUnit,
    fractionOrder_mul, neg_add, zpow_add]
  ac_rfl

@[simp] theorem angularComponent_fractionUnits {π : R} (hπ : Irreducible π) (u : Rˣ) :
    angularComponent hπ (fractionUnits R K u) = u := by
  apply fractionUnits_injective R K
  simp [fractionUnits_angularComponent, normalizedUnit]

@[simp] theorem angularComponent_uniformizer {π : R} (hπ : Irreducible π) :
    angularComponent hπ (uniformizerUnit (K := K) hπ) = 1 := by
  apply fractionUnits_injective R K
  simp [fractionUnits_angularComponent, normalizedUnit]

/-- The normalized unit component changes by the exact expected power when
the chosen uniformizer changes. -/
theorem angularComponent_change {π τ : R} (hπ : Irreducible π) (hτ : Irreducible τ)
    (x : Kˣ) :
    angularComponent hτ x = angularComponent hπ x *
      angularComponent hτ (uniformizerUnit (K := K) hπ) ^ fractionOrder R K x := by
  apply fractionUnits_injective R K
  simp only [map_mul, map_zpow, fractionUnits_angularComponent, normalizedUnit,
    fractionOrder_uniformizer, mul_zpow, inv_zpow, zpow_neg]
  group

/-- Unit reduction to the actual residue field of the DVR. -/
noncomputable def residueUnits : Rˣ →* (ResidueField R)ˣ := Units.map (residue R).toMonoidHom

/-- Positive integer order means strict membership in the valuation ideal. -/
theorem fractionValuation_lt_one_iff (x : Kˣ) :
    fractionValuation R K (x : K) < 1 ↔ 0 < fractionOrder R K x := by
  rw [fractionValuation_eq, WithZero.exp_lt_one_iff]
  omega

/-- Order zero is characterized by valuation one. -/
theorem fractionValuation_eq_one_iff (x : Kˣ) :
    fractionValuation R K (x : K) = 1 ↔ fractionOrder R K x = 0 := by
  rw [fractionValuation_eq, ← WithZero.exp_zero, WithZero.exp_inj]
  omega

/-- Equality in the actual residue field follows from a strict valuation bound. -/
theorem residue_eq_of_fractionValuation_sub_lt (a b : R)
    (h : fractionValuation R K (algebraMap R K (a - b)) < 1) : residue R a = residue R b := by
  apply sub_eq_zero.mp
  rw [← map_sub, residue_eq_zero_iff]
  exact ((IsDiscreteValuationRing.maximalIdeal R).valuation_lt_one_iff_mem (K := K) (a - b)).mp h

/-- In a Steinberg pair, a positive-order entry forces the other entry to
be a unit congruent to one modulo the maximal ideal. -/
theorem steinberg_positive {π : R} (hπ : Irreducible π) (x y : Kˣ)
    (hxy : (x : K) + (y : K) = 1) (hx : 0 < fractionOrder R K x) :
    fractionOrder R K y = 0 ∧ residueUnits (angularComponent hπ y) = 1 := by
  have hxv : fractionValuation R K (x : K) < 1 := (fractionValuation_lt_one_iff x).2 hx
  have hyv : fractionValuation R K (y : K) = 1 := by
    have hy : (y : K) = 1 - (x : K) := by linear_combination hxy
    rw [hy]
    exact (fractionValuation R K).map_one_sub_of_lt hxv
  have hy : fractionOrder R K y = 0 := (fractionValuation_eq_one_iff y).1 hyv
  refine ⟨hy, ?_⟩
  apply Units.ext
  change residue R (angularComponent hπ y : R) = 1
  rw [← map_one (residue R)]
  apply residue_eq_of_fractionValuation_sub_lt (K := K)
  have he : algebraMap R K ((angularComponent hπ y : R) - 1) = -(x : K) := by
    rw [map_sub, map_one]
    change (fractionUnits R K (angularComponent hπ y) : K) - 1 = -(x : K)
    rw [fractionUnits_angularComponent]
    simp only [normalizedUnit, hy, neg_zero, zpow_zero, mul_one]
    linear_combination hxy
  rw [he, (fractionValuation R K).map_neg]
  exact hxv

/-- When a Steinberg pair has negative order, both orders coincide and their
normalized unit coefficients are negatives in the genuine residue field. -/
theorem steinberg_negative {π : R} (hπ : Irreducible π) (x y : Kˣ)
    (hxy : (x : K) + (y : K) = 1) (hx : fractionOrder R K x < 0) :
    fractionOrder R K y = fractionOrder R K x ∧
      residueUnits (angularComponent hπ y) = -residueUnits (angularComponent hπ x) := by
  have hxv : 1 < fractionValuation R K (x : K) := by
    rw [fractionValuation_eq, WithZero.one_lt_exp_iff]
    omega
  have hyv : fractionValuation R K (y : K) = fractionValuation R K (x : K) := by
    have hy : (y : K) = 1 - (x : K) := by linear_combination hxy
    rw [hy]
    exact (fractionValuation R K).map_sub_eq_of_lt_right (by simpa using hxv)
  have hy : fractionOrder R K y = fractionOrder R K x := by
    rw [fractionValuation_eq, fractionValuation_eq, WithZero.exp_inj] at hyv
    omega
  refine ⟨hy, ?_⟩
  apply Units.ext
  change residue R (angularComponent hπ y : R) = -residue R (angularComponent hπ x : R)
  apply eq_neg_of_add_eq_zero_right
  rw [← map_add]
  have he : algebraMap R K ((angularComponent hπ x : R) + (angularComponent hπ y : R)) =
      (uniformizerUnit (K := K) hπ ^ (-fractionOrder R K x) : Kˣ) := by
    rw [map_add]
    change (fractionUnits R K (angularComponent hπ x) : K) +
      (fractionUnits R K (angularComponent hπ y) : K) = _
    rw [fractionUnits_angularComponent, fractionUnits_angularComponent]
    simp only [normalizedUnit, Units.val_mul, hy]
    rw [← add_mul, hxy, one_mul]
  have hv : fractionValuation R K (algebraMap R K
      ((angularComponent hπ x : R) + (angularComponent hπ y : R))) < 1 := by
    rw [he, fractionValuation_lt_one_iff]
    simp only [fractionOrder_zpow, fractionOrder_uniformizer, mul_one]
    omega
  have hr := residue_eq_of_fractionValuation_sub_lt (K := K)
    ((angularComponent hπ x : R) + (angularComponent hπ y : R)) 0 (by simpa using hv)
  simpa using hr

/-- Every nonzero residue-field element lifts to a unit of the actual DVR. -/
theorem residueUnits_surjective : Function.Surjective (residueUnits (R := R)) := by
  intro a
  obtain ⟨r, hr⟩ := residue_surjective (R := R) (a : ResidueField R)
  have hu : IsUnit r := (residue_ne_zero_iff_isUnit r).mp (by rw [hr]; exact a.ne_zero)
  refine ⟨hu.unit, ?_⟩
  apply Units.ext
  simpa [residueUnits, hu.unit_spec] using hr

variable (R K)

/-- The canonical fraction order as an integer-linear map on additive unit notation. -/
noncomputable def fractionOrderLinear : Additive Kˣ →ₗ[ℤ] ℤ :=
  ({ toFun := fun a => fractionOrder R K a.toMul
     map_zero' := fractionOrder_one R K
     map_add' := fun a b => fractionOrder_mul R K a.toMul b.toMul } :
    Additive Kˣ →+ ℤ).toIntLinearMap

@[simp] theorem fractionOrderLinear_apply (a : Kˣ) :
    fractionOrderLinear R K (Additive.ofMul a) = fractionOrder R K a := rfl

@[simp] theorem fractionOrderLinear_fractionUnits (a : Rˣ) :
    fractionOrderLinear R K (Additive.ofMul (fractionUnits R K a)) = 0 :=
  fractionOrder_fractionUnits R K a

@[simp] theorem fractionOrderLinear_uniformizer {π : R} (hπ : Irreducible π) :
    fractionOrderLinear R K (Additive.ofMul (uniformizerUnit (K := K) hπ)) = 1 :=
  fractionOrder_uniformizer hπ

variable {R K}

/-- The angular component bundled with its proved multiplicative law. -/
noncomputable def angularComponentHom {π : R} (hπ : Irreducible π) : Kˣ →* Rˣ where
  toFun := angularComponent hπ
  map_one' := by
    apply fractionUnits_injective R K
    simp [fractionUnits_angularComponent, normalizedUnit]
  map_mul' := angularComponent_mul hπ

/-- Actual reduction of the angular component in the literal residue field. -/
noncomputable def angularResidue {π : R} (hπ : Irreducible π) :
    Kˣ →* (ResidueField R)ˣ :=
  (residueUnits (R := R)).comp (angularComponentHom (K := K) hπ)

/-- The same actual residue map in integer-linear additive notation. -/
noncomputable def angularResidueLinear {π : R} (hπ : Irreducible π) :
    Additive Kˣ →ₗ[ℤ] Additive (ResidueField R)ˣ :=
  (angularResidue (K := K) hπ).toAdditive.toIntLinearMap

@[simp] theorem angularResidue_fractionUnits {π : R} (hπ : Irreducible π) (u : Rˣ) :
    angularResidue (K := K) hπ (fractionUnits R K u) = residueUnits u := by
  change residueUnits (angularComponent hπ (fractionUnits R K u)) = residueUnits u
  rw [angularComponent_fractionUnits]

end IsDiscreteValuationRing
