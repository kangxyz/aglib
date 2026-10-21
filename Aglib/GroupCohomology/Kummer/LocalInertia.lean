/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupCohomology.Kummer.InertiaCharacter
public import Aglib.RingTheory.IntegralClosure.Inertia.Finite
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Kummer root ratios over inertia-fixed local fields

Let L be an actual intermediate field of AlgebraicClosure K, where K has characteristic zero
and is the fraction field of the DVR R. The supplied absolute prime Q is maximal above the
maximal ideal of R. Original inertia is independently required to fix every element of L. At a
positive level invertible in R, roots of units in the localization of integralClosure R L at
the contraction of Q are fixed by inertia. The root-ratio formula additionally requires this
localization to be a DVR with fraction field L and the image of the same R-uniformizer to be
irreducible.

Extraction source: `R5Lab.Aglib.GroupCohomology.Kummer.LocalInertia`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`c154d443e1813a301c45c799ce77024510d0af412fee288335c8ae04818b765a`.
The source conditions, actual objects and canonical maps are retained under native names.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

namespace GroupCohomology.Kummer.LocalInertia

open integralClosure.Inertia GroupCohomology.Kummer Field.absoluteGaloisGroup.RootsOfUnity
open integralClosure.Inertia.FiniteRestriction
open IsLocalRing
attribute [local instance] Ideal.Quotient.field

universe u v
variable (R : Type u) (K : Type v) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [Field K] [CharZero K]
  [Algebra R K] [IsFractionRing R K]

local notation "Ω" => AlgebraicClosure K
local notation "Γ" => Field.absoluteGaloisGroup K
local notation "Rbar" => IntegralModel R K

/-- The actual ambient field automorphism action used for local root calculations. -/
local instance closureGaloisAction : MulSemiringAction Γ Ω :=
  inferInstanceAs (MulSemiringAction (Ω ≃ₐ[K] Ω) Ω)

variable (L : IntermediateField K (AlgebraicClosure K))
  [Algebra R L] [IsScalarTower R K L] [IsScalarTower R L (AlgebraicClosure K)]
  (Q : Ideal (IntegralModel R K)) [Q.IsMaximal]
  [Q.LiesOver (maximalIdeal R)]
  (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R))

local notation "B" => integralClosure R L
local notation "P" => Q.comap (modelMap R L Ω)
local notation "I" => inertia R K Q

/-- The contraction of the supplied absolute prime along the literal model map is prime. -/
local instance contractedPrimeIsPrime : (P).IsPrime := Ideal.comap_isPrime _ Q

include hn hnunit in
set_option linter.unusedSectionVars false in
-- Retain every original local-field and lying-over hypothesis in this interface.
/-- Clearing a denominator outside the original prime reduces the nth root
of a local unit to the original integral-closure residue-injectivity argument. -/
@[nolint unusedArguments]
theorem root_of_fraction_fixed
    (hfixed : ∀ σ : I, ∀ x : L, σ.val • algebraMap L Ω x = algebraMap L Ω x)
    (a b : B) (ha : modelMap R L Ω a ∉ Q) (hb : modelMap R L Ω b ∉ Q)
    (γ : Ω) (hγ : γ ^ n * algebraMap L Ω (b : L) = algebraMap L Ω (a : L))
    (σ : I) : σ.val • γ = γ := by
  let d : Ω := γ * algebraMap L Ω (b : L)
  have hd : d ^ n = algebraMap L Ω (a : L) * algebraMap L Ω (b : L) ^ (n - 1) := by
    dsimp [d]
    rw [mul_pow]
    calc
      γ ^ n * algebraMap L Ω (b : L) ^ n =
          (γ ^ n * algebraMap L Ω (b : L)) * algebraMap L Ω (b : L) ^ (n - 1) := by
        rw [mul_assoc, ← pow_succ']
        rw [Nat.sub_add_cancel hn]
      _ = _ := by rw [hγ]; rfl
  have hdint : IsIntegral R d := by
    apply IsIntegral.of_pow hn
    rw [hd]
    exact (modelMap R L Ω a).property.mul ((modelMap R L Ω b).property.pow (n - 1))
  let δ : Rbar := ⟨d, hdint⟩
  have hδ : δ ^ n = modelMap R L Ω a * modelMap R L Ω b ^ (n - 1) := Subtype.ext hd
  have hδnonzero : Ideal.Quotient.mk Q δ ≠ 0 := by
    intro he
    have he' := congrArg (Ideal.Quotient.mk Q) hδ
    rw [map_pow, he, zero_pow hn.ne', map_mul, map_pow] at he'
    exact (mul_ne_zero (Ideal.Quotient.eq_zero_iff_mem.not.mpr ha)
      (pow_ne_zero _ (Ideal.Quotient.eq_zero_iff_mem.not.mpr hb))) he'.symm
  have hpow : (σ.val • δ) ^ n = δ ^ n := by
    rw [← smul_pow', hδ]
    apply Subtype.ext
    change σ.val • (algebraMap L Ω (a : L) * algebraMap L Ω (b : L) ^ (n - 1)) = _
    rw [smul_mul', smul_pow', hfixed σ a.val, hfixed σ b.val]
    rfl
  have hres : Ideal.Quotient.mk Q (σ.val • δ) = Ideal.Quotient.mk Q δ :=
    Ideal.Quotient.eq.mpr (σ.property δ)
  have heq := eq_of_power_eq_of_residue_eq Q n
    (Ideal.notMem_of_isUnit Q (show IsUnit (n : Rbar) by
      simpa only [map_natCast] using hnunit.map (algebraMap R Rbar))) hpow hδnonzero hres
  have heq' := congrArg Subtype.val heq
  change σ.val • (γ * algebraMap L Ω (b : L)) = γ * algebraMap L Ω (b : L) at heq'
  rw [smul_mul', hfixed σ b.val] at heq'
  have hb0 : algebraMap L Ω (b : L) ≠ 0 := by
    intro hb0
    have hb' : modelMap R L Ω b = 0 := Subtype.ext hb0
    exact hb (hb' ▸ Q.zero_mem)
  exact mul_right_cancel₀ hb0 heq'

include hn hnunit in
/-- Original inertia fixes nth roots of units of the localization of an
inertia-fixed subfield's integral closure at the contraction of original Q. -/
theorem localUnit_root_fixed
    (S : Type*) [CommRing S] [Algebra B S] [IsLocalization.AtPrime S P]
    [Algebra S L] [IsScalarTower B S L]
    (hfixed : ∀ σ : I, ∀ x : L, σ.val • algebraMap L Ω x = algebraMap L Ω x)
    (u : Sˣ) (γ : Ω)
    (hγ : γ ^ n = algebraMap L Ω (algebraMap S L (u : S)))
    (σ : I) : σ.val • γ = γ := by
  obtain ⟨a, b, hu⟩ := IsLocalization.exists_mk'_eq (P).primeCompl (u : S)
  have ha : a ∈ (P).primeCompl := (IsLocalization.AtPrime.isUnit_mk'_iff S P a b).mp (by
    rw [hu]
    exact u.isUnit)
  apply root_of_fraction_fixed R K L Q n hn hnunit hfixed a b ha b.property γ ?_ σ
  have hspec := IsLocalization.mk'_spec S a b
  rw [hu] at hspec
  have hspec' := congrArg (algebraMap S L) hspec
  rw [map_mul, ← IsScalarTower.algebraMap_apply B S L,
    ← IsScalarTower.algebraMap_apply B S L] at hspec'
  have hspec'' := congrArg (algebraMap L Ω) hspec'
  rw [map_mul, ← hγ] at hspec''
  exact hspec''

-- Retain the specified R-to-integral-closure-to-S scalar tower of the source interface.
/-- The unit/uniformizer decomposition in the unramified local extension
computes the original inertia ratio of an actual nth root in the same closure. -/
@[nolint unusedArguments]
theorem root_ratio_order
    (S : Type*) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Algebra B S] [IsLocalization.AtPrime S P]
    [Algebra R S] [IsScalarTower R B S]
    [Algebra S L] [IsScalarTower B S L] [IsScalarTower R S L]
    [IsFractionRing S L]
    (hfixed : ∀ σ : I, ∀ x : L, σ.val • algebraMap L Ω x = algebraMap L Ω x)
    {π : R} (hπ : Irreducible π) (hπS : Irreducible (algebraMap R S π))
    (u : Lˣ) (β : Ωˣ)
    (hβ : β ^ n = Units.map (algebraMap L Ω).toMonoidHom u)
    (σ : I) :
    Kummer.unitAction K σ.val β / β =
      (((tameCharacter R K Q n hn hnunit hπ σ).toAdd).toMul : Ωˣ) ^
        IsDiscreteValuationRing.fractionOrder S L u := by
  let m := IsDiscreteValuationRing.fractionOrder S L u
  let v := IsDiscreteValuationRing.angularComponent hπS u
  let α := Kummer.chosenRoot K n hn (IsDiscreteValuationRing.uniformizerUnit (K := K) hπ)
  have hα : α ^ n = Units.map (algebraMap L Ω).toMonoidHom
      (IsDiscreteValuationRing.uniformizerUnit (K := L) hπS) := by
    rw [Kummer.chosenRoot_pow]
    apply Units.ext
    change algebraMap K Ω (algebraMap R K π) =
      algebraMap L Ω (algebraMap S L (algebraMap R S π))
    rw [← IsScalarTower.algebraMap_apply R K Ω,
      ← IsScalarTower.algebraMap_apply R S L,
      ← IsScalarTower.algebraMap_apply R L Ω]
  have hdec : IsDiscreteValuationRing.fractionUnits S L v *
      IsDiscreteValuationRing.uniformizerUnit (K := L) hπS ^ m = u := by
    rw [IsDiscreteValuationRing.fractionUnits_angularComponent]
    simp [IsDiscreteValuationRing.normalizedUnit, m, mul_assoc]
  let γ := β / α ^ m
  have hγ : γ ^ n = Units.map (algebraMap L Ω).toMonoidHom
      (IsDiscreteValuationRing.fractionUnits S L v) := by
    dsimp [γ]
    have hcomm : (α ^ m) ^ n = (α ^ n) ^ m := by
      simpa only [zpow_natCast] using zpow_comm α m (n : ℤ)
    rw [div_pow, hcomm, hβ, hα, ← map_zpow, ← map_div]
    congr 1
    rw [← hdec]
    exact mul_div_cancel_right _ _
  have hγfix : Kummer.unitAction K σ.val γ = γ := by
    apply Units.ext
    exact localUnit_root_fixed R K L Q n hn hnunit S hfixed v (γ : Ω)
      (congrArg Units.val hγ) σ
  have hratio : Kummer.unitAction K σ.val β / β =
      (Kummer.unitAction K σ.val α / α) ^ m := by
    change Kummer.unitAction K σ.val (β / α ^ m) = β / α ^ m at hγfix
    rw [map_div, map_zpow] at hγfix
    have hβ' : Kummer.unitAction K σ.val β =
        (β / α ^ m) * (Kummer.unitAction K σ.val α) ^ m :=
      (div_eq_iff_eq_mul).mp hγfix
    rw [hβ', div_zpow]
    simp only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
    exact mul_inv_cancel_left _ _
  exact hratio

end GroupCohomology.Kummer.LocalInertia
