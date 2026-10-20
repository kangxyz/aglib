/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.DiscreteValuationRing.AngularComponent
public import Mathlib.RingTheory.RootsOfUnity.Basic

/-!
# Canonical DVR lifts and residue roots

Source: `R5Lab.Aglib.RingTheory.RootsOfUnity.DVR`,
revision `f8a3314ddecffcada2ec721d26d56a937bed9690`. Exact field, action, embedding and
explicit-data hypotheses are retained. Native objects and maps are reused.
-/

@[expose] public section

noncomputable section

namespace IsDiscreteValuationRing.RootsOfUnity

open IsLocalRing

universe u v

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

/-- Every element of positive finite multiplicative order has DVR order zero. -/
theorem order_eq_zero_of_pow_eq_one {n : ℕ} (hn : 0 < n) (x : Kˣ) (hx : x ^ n = 1) :
    IsDiscreteValuationRing.fractionOrder R K x = 0 := by
  have h : (n : ℤ) * IsDiscreteValuationRing.fractionOrder R K x = 0 := by
    rw [← IsDiscreteValuationRing.fractionOrder_zpow, zpow_natCast, hx,
      IsDiscreteValuationRing.fractionOrder_one]
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  exact (mul_eq_zero.mp h).resolve_left hn'

/-- A root of unity has zero integer valuation. -/
@[simp] theorem order_root {n : ℕ} (hn : 0 < n) (z : rootsOfUnity n K) :
    IsDiscreteValuationRing.fractionOrder R K (z : Kˣ) = 0 :=
  order_eq_zero_of_pow_eq_one R K hn z z.property

/-- The unique DVR unit whose fraction-field image is the given root of unity.
The definition does not select or mention a uniformizer. -/
def rootLift {n : ℕ} (hn : 0 < n) (z : rootsOfUnity n K) : Rˣ :=
  (IsDiscreteValuationRing.exists_fractionUnit_of_fractionOrder_zero (z : Kˣ) (order_root R K hn
    z)).choose

@[simp] theorem fractionUnits_rootLift {n : ℕ} (hn : 0 < n) (z : rootsOfUnity n K) :
    IsDiscreteValuationRing.fractionUnits R K (rootLift R K hn z) = (z : Kˣ) :=
  (IsDiscreteValuationRing.exists_fractionUnit_of_fractionOrder_zero (z : Kˣ) (order_root R K hn
    z)).choose_spec

/-- Characterization by its fraction-field image proves uniqueness of the lift. -/
theorem rootLift_unique {n : ℕ} (hn : 0 < n) (z : rootsOfUnity n K) (a : Rˣ)
    (ha : IsDiscreteValuationRing.fractionUnits R K a = (z : Kˣ)) : a = rootLift R K hn z := by
  apply IsDiscreteValuationRing.fractionUnits_injective R K
  rw [ha, fractionUnits_rootLift]

/-- The canonical lift agrees with the angular component for every actual uniformizer. -/
theorem rootLift_eq_angularComponent {n : ℕ} (hn : 0 < n) (z : rootsOfUnity n K)
    {π : R} (hπ : Irreducible π) :
    rootLift R K hn z = IsDiscreteValuationRing.angularComponent hπ (z : Kˣ) := by
  apply IsDiscreteValuationRing.fractionUnits_injective R K
  rw [fractionUnits_rootLift, IsDiscreteValuationRing.fractionUnits_angularComponent]
  simp [IsDiscreteValuationRing.normalizedUnit, order_root R K hn z]

/-- Thus angular components of roots coincide for any two uniformizers. -/
theorem angularComponent_root_independent {n : ℕ} (hn : 0 < n) (z : rootsOfUnity n K)
    {π τ : R} (hπ : Irreducible π) (hτ : Irreducible τ) :
    IsDiscreteValuationRing.angularComponent hπ (z : Kˣ) =
      IsDiscreteValuationRing.angularComponent hτ (z : Kˣ) := by
  rw [← rootLift_eq_angularComponent R K hn z hπ,
    ← rootLift_eq_angularComponent R K hn z hτ]

@[simp] theorem rootLift_one {n : ℕ} (hn : 0 < n) : rootLift R K hn 1 = 1 := by
  apply IsDiscreteValuationRing.fractionUnits_injective R K
  simp

@[simp] theorem rootLift_mul {n : ℕ} (hn : 0 < n) (z w : rootsOfUnity n K) :
    rootLift R K hn (z * w) = rootLift R K hn z * rootLift R K hn w := by
  apply IsDiscreteValuationRing.fractionUnits_injective R K
  simp

/-- Canonical lifting is a homomorphism on the actual group of roots of unity. -/
def rootLiftHom {n : ℕ} (hn : 0 < n) : rootsOfUnity n K →* Rˣ where
  toFun := rootLift R K hn
  map_one' := rootLift_one R K hn
  map_mul' := rootLift_mul R K hn

/-- The canonical lifted unit is itself an n-th root in the DVR. -/
@[simp] theorem rootLift_pow {n : ℕ} (hn : 0 < n) (z : rootsOfUnity n K) :
    rootLift R K hn z ^ n = 1 := by
  apply IsDiscreteValuationRing.fractionUnits_injective R K
  simp only [map_pow, fractionUnits_rootLift, map_one]
  exact z.property

/-- The residue root, in the actual residue field of the DVR. -/
def residueRoot {n : ℕ} (hn : 0 < n) (z : rootsOfUnity n K) : rootsOfUnity n (ResidueField R) :=
  ⟨IsDiscreteValuationRing.residueUnits (rootLift R K hn z), by
    change IsDiscreteValuationRing.residueUnits (rootLift R K hn z) ^ n = 1
    rw [← map_pow, rootLift_pow, map_one]⟩

@[simp] theorem residueRoot_val {n : ℕ} (hn : 0 < n) (z : rootsOfUnity n K) :
    (residueRoot R K hn z : (ResidueField R)ˣ) =
      IsDiscreteValuationRing.residueUnits (rootLift R K hn z) := rfl

/-- The residue root satisfies the requested n-th power equation. -/
@[simp] theorem residueRoot_pow {n : ℕ} (hn : 0 < n) (z : rootsOfUnity n K) :
    (residueRoot R K hn z : (ResidueField R)ˣ) ^ n = 1 :=
  (residueRoot R K hn z).property

/-- Reduction of roots is a canonical group homomorphism. -/
def residueRootHom {n : ℕ} (hn : 0 < n) : rootsOfUnity n K →* rootsOfUnity n (ResidueField R) where
  toFun := residueRoot R K hn
  map_one' := by apply Subtype.ext; simp
  map_mul' z w := by apply Subtype.ext; simp

end IsDiscreteValuationRing.RootsOfUnity
