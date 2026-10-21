/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.GroupCohomology.Kummer.InertiaCharacter
public import Aglib.RingTheory.RootsOfUnity.Exactness
public import Aglib.RingTheory.IntegralClosure.Inertia.Etale
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.RingTheory.Multiplicity
public import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Surjectivity of the actual uniformizer tame character

The uniformizer Kummer character on actual inertia is surjective in characteristic zero at each
positive level invertible in the DVR R. The fraction field, supplied prime above the maximal
ideal, and chosen irreducible uniformizer are retained. The proof first derives divisibility of
exponents in a finite faithful formally unramified Dedekind R-algebra. Its normalization
argument requires every embedding of the root-generated field to be fixed by original inertia;
fixedness of the displayed root alone is propagated to that full quantifier before the
etaleness theorem is applied.

Extraction source: `R5Lab.Aglib.GroupCohomology.Kummer.TameSurjectivity`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`b8a7579e9f2a4d1de414c380930ab8bda48bba45fbffd93486c6a96d7fa53eaa`.
The source conditions, actual objects and canonical maps are retained under native names.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open integralClosure.Inertia
open IsLocalRing
open Field.absoluteGaloisGroup.RootsOfUnity
open integralClosure.Inertia.FiniteRestriction
open scoped IntermediateField

namespace GroupCohomology.Kummer

universe u v

/-- A root-power relation in a formally unramified Dedekind extension forces
the same divisibility of exponents as in the original DVR. The localization
is taken at the supplied prime, not a replacement prime. -/
theorem dvd_exponent_of_unramified_root
    (R : Type u) (B : Type v) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing B] [IsDedekindDomain B] [Algebra R B]
    [Module.Finite R B] [FaithfulSMul R B]
    [Algebra.FormallyUnramified R B]
    (P : Ideal B) [P.IsPrime] [P.LiesOver (maximalIdeal R)]
    {π : R} (hπ : Irreducible π) (b : B) (n m : ℕ)
    (hb : b ^ n = algebraMap R B π ^ m) : n ∣ m := by
  have hP : P ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot
    (IsDiscreteValuationRing.not_a_field R) P
  let S := Localization.AtPrime P
  have : IsDiscreteValuationRing S :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain B hP S
  have : IsLocalHom (algebraMap R S) := by
    apply ((local_hom_TFAE (algebraMap R S)).out 1 5).mpr
    rw [IsScalarTower.algebraMap_eq R B S, ← Ideal.comap_comap]
    change ((maximalIdeal S).under B).under R = _
    rw [IsLocalization.AtPrime.under_maximalIdeal S P]
    exact Ideal.LiesOver.over.symm
  have hπS : Irreducible (algebraMap R S π) := by
    apply (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := S),
      hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  have hbS : algebraMap B S b ^ n = algebraMap R S π ^ m := by
    simpa only [map_pow, ← IsScalarTower.algebraMap_apply R B S] using
      congrArg (algebraMap B S) hb
  have hv := congrArg (emultiplicity (algebraMap R S π)) hbS
  rw [emultiplicity_pow (irreducible_iff_prime.mp hπS),
    emultiplicity_pow_self hπS.ne_zero hπS.not_isUnit] at hv
  have hnat := congrArg ENat.toNat hv
  rw [ENat.toNat_mul] at hnat
  simp only [ENat.toNat_natCast] at hnat
  exact ⟨(emultiplicity (algebraMap R S π) (algebraMap B S b)).toNat, hnat.symm⟩

section Roots

variable (R : Type u) (K : Type v) [CommRing R] [Field K] [Algebra R K]
  (Q : Ideal (integralClosure.Inertia.IntegralModel R K)) [Q.IsPrime]
  (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R))

include hn hnunit in
/-- Since the original inertia fixes actual roots of unity, if it fixes one
root of a specified field unit then it fixes every conjugate root. -/
theorem fixed_conjugate_root {f : Kˣ} (b c : (AlgebraicClosure K)ˣ)
    (hb : b ^ n = Kummer.baseUnits K f) (hc : c ^ n = Kummer.baseUnits K f)
    (σ : integralClosure.Inertia.inertia R K Q) (hfixed : Kummer.unitAction K σ.val b = b) :
    Kummer.unitAction K σ.val c = c := by
  have h := congrArg (fun z : Mu K n => (z.toMul : (AlgebraicClosure K)ˣ))
    (integralClosure.Inertia.inertia_fixes_roots R K Q n hn hnunit
      (Kummer.rootRatio K n b hb c hc) σ)
  change Kummer.unitAction K σ.val (c / b) = c / b at h
  rw [map_div, hfixed] at h
  exact (div_left_inj).mp h

variable [CharZero K]

include hn hnunit in
/-- Every embedding of the same root-generated field is fixed by the original
inertia. The embedding is extended to an actual ambient field automorphism;
its conjugate root differs by an actual inertia-fixed root of unity. -/
theorem root_field_embeddings_fixed {f : Kˣ} (b : (AlgebraicClosure K)ˣ)
    (hb : b ^ n = Kummer.baseUnits K f)
    (hfixed : ∀ σ : integralClosure.Inertia.inertia R K Q, Kummer.unitAction K σ.val b = b) :
    ∀ σ ∈ Q.inertia (AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K),
      ∀ φ : K⟮(b : AlgebraicClosure K)⟯ →ₐ[K] AlgebraicClosure K,
      σ.toAlgHom.comp φ = φ := by
  intro σ hσ φ
  let L := K⟮(b : AlgebraicClosure K)⟯
  let β : L := ⟨(b : AlgebraicClosure K), IntermediateField.subset_adjoin K _
    (Set.mem_singleton _)⟩
  let Φ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K :=
    AlgEquiv.ofBijective (φ.liftNormal (AlgebraicClosure K))
      (AlgHom.normal_bijective K (AlgebraicClosure K) (AlgebraicClosure K) _)
  have hext : Φ (b : AlgebraicClosure K) = φ β := by
    change (φ.liftNormal (AlgebraicClosure K)) (algebraMap L (AlgebraicClosure K) β) = φ β
    simpa using φ.liftNormal_commutes (AlgebraicClosure K) β
  have hc : Kummer.unitAction K Φ b ^ n = Kummer.baseUnits K f := by
    rw [← map_pow, hb]
    exact Kummer.unitAction_base K (show Field.absoluteGaloisGroup K from Φ) f
  have hconj := fixed_conjugate_root R K Q n hn hnunit b
    (Kummer.unitAction K Φ b) hb hc ⟨σ, hσ⟩ (hfixed ⟨σ, hσ⟩)
  apply IntermediateField.adjoin_algHom_ext K
  intro x hx
  obtain rfl := Set.mem_singleton_iff.mp hx
  change σ (φ β) = φ β
  rw [← hext]
  exact congrArg Units.val hconj

end Roots

section DVR

variable (R : Type u) (K : Type v) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K]
  (Q : Ideal (integralClosure.Inertia.IntegralModel R K)) [Q.IsPrime]
  [Q.LiesOver (maximalIdeal R)]
  (n : ℕ) (hn : 0 < n) (hnunit : IsUnit (n : R))

include hn hnunit in
/-- An inertia-fixed root of a uniformizer power has an integral valuation.
Etaleness of its literal finite-field normalization is proved from all actual
embeddings; localization retains the contraction of the original absolute Q. -/
theorem dvd_exponent_of_inertia_fixed_root {π : R} (hπ : Irreducible π)
    (m : ℕ) (b : (AlgebraicClosure K)ˣ)
    (hb : b ^ n = Kummer.baseUnits K (IsDiscreteValuationRing.uniformizerUnit (K := K) hπ ^ m))
    (hfixed : ∀ σ : integralClosure.Inertia.inertia R K Q, Kummer.unitAction K σ.val b = b) :
    n ∣ m := by
  let L := K⟮(b : AlgebraicClosure K)⟯
  let : Algebra R L := ((algebraMap K L).comp (algebraMap R K)).toAlgebra
  have : IsScalarTower R K L := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R L (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      change algebraMap L (AlgebraicClosure K) (algebraMap K L (algebraMap R K r)) =
        algebraMap R (AlgebraicClosure K) r
      rw [← IsScalarTower.algebraMap_apply K L (AlgebraicClosure K),
        ← IsScalarTower.algebraMap_apply R K (AlgebraicClosure K)]
  have : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional
    (Algebra.IsIntegral.isIntegral (R := K) (b : AlgebraicClosure K))
  have : Algebra.Etale R (integralClosure R L) :=
    integralClosure.Inertia.NonGalois.model_etale_of_absolute_inertia_trivial_on_generic_fiber
      R K (AlgebraicClosure K) L Q (root_field_embeddings_fixed R K Q n hn hnunit b hb hfixed)
  have : IsDedekindDomain (integralClosure R L) := integralClosure.isDedekindDomain R K L
  have : Module.Finite R (integralClosure R L) := IsIntegralClosure.finite R K L _
  have : FaithfulSMul R (integralClosure R L) := by
    apply (faithfulSMul_iff_algebraMap_injective _ _).mpr
    intro x y hxy
    have hRL : Function.Injective (algebraMap R L) := by
      rw [IsScalarTower.algebraMap_eq R K L]
      exact (algebraMap K L).injective.comp (IsFractionRing.injective R K)
    apply hRL
    exact congrArg Subtype.val hxy
  let β : L := ⟨(b : AlgebraicClosure K), IntermediateField.subset_adjoin K _
    (Set.mem_singleton _)⟩
  have hβpow : β ^ n = algebraMap R L π ^ m := by
    apply (algebraMap L (AlgebraicClosure K)).injective
    simp only [map_pow, ← IsScalarTower.algebraMap_apply R L (AlgebraicClosure K)]
    change (b : AlgebraicClosure K) ^ n = algebraMap R (AlgebraicClosure K) π ^ m
    have hbval := congrArg Units.val hb
    simp only [Units.val_pow_eq_pow_val, Kummer.baseUnits, IsDiscreteValuationRing.uniformizerUnit,
      Units.coe_map, Units.val_mk0, map_pow] at hbval
    exact hbval
  have hβint : IsIntegral R β := by
    apply IsIntegral.of_pow hn
    rw [hβpow]
    exact isIntegral_algebraMap.pow m
  let βB : integralClosure R L := ⟨β, hβint⟩
  let P := Q.comap (modelMap R L (AlgebraicClosure K))
  have : P.IsPrime := Ideal.comap_isPrime _ Q
  have : P.LiesOver (maximalIdeal R) := by
    constructor
    rw [Q.over_def (maximalIdeal R)]
    rfl
  exact dvd_exponent_of_unramified_root R (integralClosure R L) P hπ βB n m
    (Subtype.ext hβpow)

/-- The exact uniformizer Kummer character of the original inertia group is
surjective, including composite levels and degree one. The proof uses the
actual image cardinality and unramified normalization of its fixed root power. -/
theorem tameCharacter_surjective {π : R} (hπ : Irreducible π) :
    Function.Surjective (GroupCohomology.Kummer.tameCharacter R K Q n hn hnunit hπ) := by
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let χ := GroupCohomology.Kummer.tameCharacter R K Q n hn hnunit hπ
  let H := χ.toMonoidHom.range
  let m := Nat.card H
  let f := IsDiscreteValuationRing.uniformizerUnit (K := K) hπ
  let a := Kummer.chosenRoot K n hn f
  have ha : a ^ n = Kummer.baseUnits K f := Kummer.chosenRoot_pow K n hn f
  have hfixed : ∀ σ : integralClosure.Inertia.inertia R K Q,
      Kummer.unitAction K σ.val (a ^ m) = a ^ m := by
    intro σ
    have hpow : χ σ ^ m = 1 := by
      exact congrArg Subtype.val (pow_card_eq_one' (x := (⟨χ σ, ⟨σ, rfl⟩⟩ : H)))
    have hratio := congrArg (fun z : Multiplicative (Mu K n) =>
      (z.toAdd.toMul : (AlgebraicClosure K)ˣ)) hpow
    change (Kummer.unitAction K σ.val a / a) ^ m = 1 at hratio
    rw [div_pow] at hratio
    rw [map_pow]
    exact div_eq_one.mp hratio
  have hb : (a ^ m) ^ n = Kummer.baseUnits K (f ^ m) := by
    rw [← pow_mul, Nat.mul_comm m n, pow_mul, ha, map_pow]
  have hdvd : n ∣ m := dvd_exponent_of_inertia_fixed_root R K Q n hn hnunit hπ
    m (a ^ m) hb hfixed
  have hcard : Nat.card (Multiplicative (Mu K n)) = n :=
    (Nat.card_congr (Multiplicative.ofAdd : Mu K n ≃ Multiplicative (Mu K n))).symm.trans
      (Field.absoluteGaloisGroup.RootsOfUnity.Exactness.mu_card K n)
  have hmpos : 0 < m := Nat.card_pos
  have hmle : m ≤ n := H.card_le_card_group.trans_eq hcard
  have hm : m = n := le_antisymm hmle (Nat.le_of_dvd hmpos hdvd)
  apply MonoidHom.range_eq_top.mp
  exact H.eq_top_of_card_eq (hm.trans hcard.symm)

end DVR

end GroupCohomology.Kummer
