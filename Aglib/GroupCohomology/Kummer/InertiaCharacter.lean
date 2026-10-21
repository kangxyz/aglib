/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.IntegralClosure.Inertia
public import Aglib.GroupCohomology.Kummer.Basic
public import Aglib.RingTheory.DiscreteValuationRing.AngularComponent

/-!
# Kummer and tame characters on actual inertia

The actual Kummer cocycle restricts to a continuous character on the inertia subgroup of the
supplied prime in integralClosure R (AlgebraicClosure K). The level is positive and invertible
in R. The character initially requires only a commutative R-algebra field K. Under the stated
DVR and fraction-field hypotheses, its value is the integer fraction order times the
uniformizer character. The uniformizer character is independent of that choice. Root uniqueness
retains the nonzero residue hypothesis and needs no residue perfectness.

Extraction source: `R5Lab.Aglib.GroupCohomology.Kummer.InertiaCharacter`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`949b2930214632e8320e70b03547f7df3b975b177ac9817003d795b92fdf83ab`.
The source conditions, actual objects and canonical maps are retained under native names.
-/

@[expose] public section

/-!
# The actual tame character from Kummer cocycles on DVR inertia

The character is constructed by restricting the continuous Kummer cocycle of
an actual uniformizer. Units have zero restricted Kummer character by
integrality and residue injectivity; the DVR decomposition then gives the
valuation formula. No residue map or comparison normalization is assumed.
-/

noncomputable section
namespace GroupCohomology.Kummer

open Field.absoluteGaloisGroup.RootsOfUnity _root_.GroupCohomology.ContinuousH1
  integralClosure.Inertia
open scoped TensorProduct

variable (R K : Type*) [CommRing R] [Field K] [Algebra R K]
variable (Q : Ideal (IntegralModel R K)) [Q.IsPrime]
variable (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R))

local notation "G" => Field.absoluteGaloisGroup K
local notation "I" => inertia R K Q
local notation "Kbar" => AlgebraicClosure K

/-- Restriction of a genuine Kummer cocycle is a homomorphism because inertia fixes its roots. -/
def rootCharacter {f : Kˣ} (a : (AlgebraicClosure K)ˣ) (ha : a ^ n = Kummer.baseUnits K f) :
    ContinuousMonoidHom I (Multiplicative (Mu K n)) where
  toFun g := Multiplicative.ofAdd (Kummer.value K n a ha g.val)
  map_one' := by
    change (Kummer.cocycle K n a ha).val 1 = 0
    exact _root_.GroupCohomology.ContinuousH1.Cocycle.map_one _
  map_mul' g h := by
    change Kummer.value K n a ha (g.val * h.val) =
      Kummer.value K n a ha g.val + Kummer.value K n a ha h.val
    rw [Kummer.value_mul, inertia_fixes_roots R K Q n hn hnunit]
  continuous_toFun :=
    continuous_ofAdd.comp ((Kummer.value_continuous K n a ha).comp continuous_subtype_val)

/-- The actual restricted character is independent of the selected nth root. -/
theorem rootCharacter_independent {f : Kˣ} (a b : (AlgebraicClosure K)ˣ)
    (ha : a ^ n = Kummer.baseUnits K f) (hb : b ^ n = Kummer.baseUnits K f) :
    rootCharacter R K Q n hn hnunit b hb = rootCharacter R K Q n hn hnunit a ha := by
  apply ContinuousMonoidHom.ext
  intro g
  change Kummer.value K n b hb g.val = Kummer.value K n a ha g.val
  apply sub_eq_zero.mp
  have h := congrArg (fun c : _root_.GroupCohomology.ContinuousH1.Cocycle G (Mu K n) => c.val g.val)
    (Kummer.cocycle_sub K n a ha b hb)
  change Kummer.value K n b hb g.val - Kummer.value K n a ha g.val =
    g.val • Kummer.rootRatio K n a ha b hb - Kummer.rootRatio K n a ha b hb at h
  rw [inertia_fixes_roots R K Q n hn hnunit, sub_self] at h
  exact h

/-- Kummer's continuous inertia character, constructed from an actual root. -/
def inertiaKummer (f : Kˣ) : ContinuousMonoidHom I (Multiplicative (Mu K n)) :=
  rootCharacter R K Q n hn hnunit (Kummer.chosenRoot K n hn f) (Kummer.chosenRoot_pow K n hn f)

theorem inertiaKummer_eq_rootCharacter {f : Kˣ} (a : (AlgebraicClosure K)ˣ)
    (ha : a ^ n = Kummer.baseUnits K f) :
    inertiaKummer R K Q n hn hnunit f = rootCharacter R K Q n hn hnunit a ha :=
  rootCharacter_independent R K Q n hn hnunit a (Kummer.chosenRoot K n hn f)
    ha (Kummer.chosenRoot_pow K n hn f)

/-- Multiplication of field units is addition of their actual inertia characters. -/
theorem inertiaKummer_mul (f f' : Kˣ) :
    inertiaKummer R K Q n hn hnunit (f * f') =
      inertiaKummer R K Q n hn hnunit f * inertiaKummer R K Q n hn hnunit f' := by
  let a := Kummer.chosenRoot K n hn f
  let b := Kummer.chosenRoot K n hn f'
  have ha : a ^ n = Kummer.baseUnits K f := Kummer.chosenRoot_pow K n hn f
  have hb : b ^ n = Kummer.baseUnits K f' := Kummer.chosenRoot_pow K n hn f'
  have hab : (a * b) ^ n = Kummer.baseUnits K (f * f') := by rw [mul_pow, ha, hb, map_mul]
  rw [inertiaKummer_eq_rootCharacter R K Q n hn hnunit (a * b) hab]
  apply ContinuousMonoidHom.ext
  intro g
  change Kummer.value K n (a * b) hab g.val =
    Kummer.value K n a ha g.val + Kummer.value K n b hb g.val
  exact congrArg (fun c : _root_.GroupCohomology.ContinuousH1.Cocycle G (Mu K n) => c.val g.val)
    (Kummer.cocycle_mul K n a ha b hb)

@[simp] theorem inertiaKummer_one : inertiaKummer R K Q n hn hnunit 1 = 1 := by
  rw [inertiaKummer_eq_rootCharacter R K Q n hn hnunit 1 (by simp)]
  apply ContinuousMonoidHom.ext
  intro g
  apply Additive.toMul.injective
  apply Subtype.ext
  change Kummer.unitAction K g.val 1 / 1 = 1
  simp

/-- The actual inertia-Kummer construction as a homomorphism. -/
def inertiaKummerHom : Kˣ →* ContinuousMonoidHom I (Multiplicative (Mu K n)) where
  toFun := inertiaKummer R K Q n hn hnunit
  map_one' := inertiaKummer_one R K Q n hn hnunit
  map_mul' := inertiaKummer_mul R K Q n hn hnunit

/-- Geometric-sum uniqueness for equal roots of a unit modulo a prime away from `n`. -/
theorem eq_of_power_eq_of_residue_eq {D : Type*} [CommRing D] [IsDomain D]
    (q : Ideal D) [q.IsPrime] (m : ℕ) (hm : (m : D) ∉ q)
    {x y : D} (hp : x ^ m = y ^ m)
    (hy : Ideal.Quotient.mk q y ≠ 0)
    (hxy : Ideal.Quotient.mk q x = Ideal.Quotient.mk q y) : x = y := by
  by_contra hne
  have hs : (∑ i ∈ Finset.range m, x ^ i * y ^ (m - 1 - i)) = 0 := by
    have h := geom_sum₂_mul x y m
    rw [hp, sub_self] at h
    exact (mul_eq_zero.mp h).resolve_right (sub_ne_zero.mpr hne)
  have hs' := congrArg (Ideal.Quotient.mk q) hs
  rw [RingHom.map_geom_sum₂, hxy, geom_sum₂_self, map_zero] at hs'
  have hm' : (m : D ⧸ q) ≠ 0 := by
    intro h
    apply hm
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_natCast] using h
  exact (mul_ne_zero hm' (pow_ne_zero _ hy)) hs'

/-- An actual root of a DVR unit belongs to the integral closure. -/
def unitRootElement (u : Rˣ) (a : (AlgebraicClosure K)ˣ)
    (ha : a ^ n = Kummer.baseUnits K (IsDiscreteValuationRing.fractionUnits R K u)) :
      IntegralModel R K := by
  refine ⟨(a : Kbar), ?_⟩
  apply IsIntegral.of_pow hn
  have hp : (a : Kbar) ^ n = algebraMap R Kbar (u : R) :=
    congrArg (fun v : (AlgebraicClosure K)ˣ => (v : Kbar)) ha
  rw [hp]
  exact isIntegral_algebraMap

@[simp] theorem unitRootElement_pow (u : Rˣ) (a : (AlgebraicClosure K)ˣ)
    (ha : a ^ n = Kummer.baseUnits K (IsDiscreteValuationRing.fractionUnits R K u)) :
    unitRootElement R K n hn u a ha ^ n = algebraMap R (IntegralModel R K) (u : R) := by
  apply Subtype.ext
  exact congrArg (fun v : (AlgebraicClosure K)ˣ => (v : Kbar)) ha

include hn hnunit in
/-- Every actual nth root of a DVR unit is fixed by inertia away from `n`. -/
theorem inertia_fixes_unit_root (u : Rˣ) (a : (AlgebraicClosure K)ˣ)
    (ha : a ^ n = Kummer.baseUnits K (IsDiscreteValuationRing.fractionUnits R K u)) (g : I) :
    Kummer.unitAction K g.val a = a := by
  let z := unitRootElement R K n hn u a ha
  have hz : z ^ n = algebraMap R (IntegralModel R K) (u : R) :=
    unitRootElement_pow R K n hn u a ha
  have hnB : IsUnit (n : IntegralModel R K) := by
    simpa using hnunit.map (algebraMap R (IntegralModel R K))
  have hy : Ideal.Quotient.mk Q z ≠ 0 := by
    intro h
    have hpow := congrArg (Ideal.Quotient.mk Q) hz
    rw [map_pow, h, zero_pow (Nat.ne_of_gt hn)] at hpow
    exact (IsUnit.ne_zero
      ((u.isUnit.map (algebraMap R (IntegralModel R K))).map (Ideal.Quotient.mk Q))) hpow.symm
  have hp : (g.val • z) ^ n = z ^ n := by
    rw [← smul_pow', hz]
    apply Subtype.ext
    exact (show Kbar ≃ₐ[K] Kbar from g.val).commutes (algebraMap R K (u : R))
  have hres : Ideal.Quotient.mk Q (g.val • z) = Ideal.Quotient.mk Q z :=
    Ideal.Quotient.eq.mpr ((integralClosure.Inertia.mem_inertia_iff R K Q g.val).mp g.property z)
  have heq := eq_of_power_eq_of_residue_eq Q n (Ideal.notMem_of_isUnit Q hnB) hp hy hres
  apply Units.ext
  exact congrArg (fun x : IntegralModel R K => (x : Kbar)) heq

/-- The inertia-Kummer character vanishes on genuine DVR units. -/
@[simp] theorem inertiaKummer_unit (u : Rˣ) :
    inertiaKummer R K Q n hn hnunit (IsDiscreteValuationRing.fractionUnits R K u) = 1 := by
  apply ContinuousMonoidHom.ext
  intro g
  apply Additive.toMul.injective
  apply Subtype.ext
  change Kummer.unitAction K g.val
      (Kummer.chosenRoot K n hn (IsDiscreteValuationRing.fractionUnits R K u)) /
      Kummer.chosenRoot K n hn (IsDiscreteValuationRing.fractionUnits R K u) = 1
  rw [inertia_fixes_unit_root R K Q n hn hnunit u _ (Kummer.chosenRoot_pow K n hn _), div_self']

section DVR

variable [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R K]

/-- The tame character is the actual Kummer character of an actual uniformizer. -/
def tameCharacter {π : R} (hπ : Irreducible π) :
    ContinuousMonoidHom I (Multiplicative (Mu K n)) :=
  inertiaKummer R K Q n hn hnunit (IsDiscreteValuationRing.uniformizerUnit (K := K) hπ)

/-- The actual DVR unit/uniformizer decomposition computes every inertia-Kummer character. -/
theorem inertiaKummer_order {π : R} (hπ : Irreducible π) (f : Kˣ) :
    inertiaKummer R K Q n hn hnunit f =
      tameCharacter R K Q n hn hnunit hπ ^ IsDiscreteValuationRing.fractionOrder R K f := by
  have hdec : IsDiscreteValuationRing.fractionUnits R K
    (IsDiscreteValuationRing.angularComponent hπ f) *
      IsDiscreteValuationRing.uniformizerUnit (K := K) hπ ^
        IsDiscreteValuationRing.fractionOrder R K f = f := by
    rw [IsDiscreteValuationRing.fractionUnits_angularComponent]
    simp [IsDiscreteValuationRing.normalizedUnit, mul_assoc]
  rw [← hdec, inertiaKummer_mul, inertiaKummer_unit, one_mul]
  change inertiaKummerHom R K Q n hn hnunit (_ ^ _) = _
  rw [map_zpow]
  congr 1
  rw [hdec]

/-- Changing the actual uniformizer does not change the tame character on inertia. -/
theorem tameCharacter_independent {π τ : R} (hπ : Irreducible π) (hτ : Irreducible τ) :
    tameCharacter R K Q n hn hnunit hτ = tameCharacter R K Q n hn hnunit hπ := by
  simpa only [tameCharacter, IsDiscreteValuationRing.fractionOrder_uniformizer, zpow_one] using
    inertiaKummer_order R K Q n hn hnunit hπ (IsDiscreteValuationRing.uniformizerUnit (K := K) hτ)

/-- Every actual Kummer cocycle evaluates on inertia as the valuation times the tame character. -/
theorem kummer_value_order {π : R} (hπ : Irreducible π) {f : Kˣ}
    (a : (AlgebraicClosure K)ˣ) (ha : a ^ n = Kummer.baseUnits K f) (g : I) :
    Kummer.value K n a ha g.val =
      IsDiscreteValuationRing.fractionOrder R K f • (tameCharacter R K Q n hn hnunit hπ
        g).toAdd := by
  have h := (inertiaKummer_eq_rootCharacter R K Q n hn hnunit a ha).symm.trans
    (inertiaKummer_order R K Q n hn hnunit hπ f)
  have he := congrArg (fun c : ContinuousMonoidHom I (Multiplicative (Mu K n)) =>
    (c g).toAdd) h
  let ev : ContinuousMonoidHom I (Multiplicative (Mu K n)) →* Multiplicative (Mu K n) :=
    { toFun := fun c => c g
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hz := ev.map_zpow (tameCharacter R K Q n hn hnunit hπ)
    (IsDiscreteValuationRing.fractionOrder R K f)
  change (tameCharacter R K Q n hn hnunit hπ ^ IsDiscreteValuationRing.fractionOrder R K f) g =
    _ at hz
  change Kummer.value K n a ha g.val = _ at he
  rw [hz] at he
  exact he

end DVR
end GroupCohomology.Kummer
