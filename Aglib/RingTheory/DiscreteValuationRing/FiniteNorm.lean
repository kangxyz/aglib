/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.DiscreteValuationRing.DeterminantLength
public import Mathlib.RingTheory.Localization.NormTrace
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.OrderOfVanishing.Noetherian
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.Data.ENat.BigOperators

/-!
# Fraction norms and the finite principal-quotient decomposition

These are algebraic prerequisites for `NormDegree.FiniteMorphismNormOrder`.
For finite free domain algebras, the actual field norm on fraction fields
equals the localized determinant norm. For a base DVR the actual `Ring.ordFrac`
of this norm is the difference of the lengths of the principal quotients of
the numerator and denominator. Inseparable extensions are permitted.

The principal quotient is Artinian. Its length is the sum over all of its
prime localizations, and each summand factors as a local length times the
degree of the canonical residue-field extension. These formulas retain the
entire supporting spectrum of the quotient.

The quotient/localization comparison identifies these local lengths with the
actual `Ring.ord` on `B` localized at its maximal ideals. A proved bijection
and the zero orders of the nonsupporting branches then give the sum over ALL
maximal ideals of `B`. Finiteness of this maximal spectrum is proved from the
finite algebra hypothesis. No perfectness, separability, Galois or Dedekind
assumption on `B` is used in this algebraic norm formula.

When every maximal localization of `B` is a DVR, the final theorem
`fieldNorm_order_eq_sum_all_maximal` gives the norm/order identity for every
unit of the actual fraction field of `B`, using the canonical fraction-field
algebras on each branch and the actual residue-field maps. The finite free
property of `B` is derived from its finite-domain and fraction-field data.

Constructing `B` as the full finite inverse image of a scheme stalk and
identifying its fractions, branches, stalks and residue maps with the actual
scheme data remain open. No theorem here asserts the universal geometric
norm/order family.
-/

@[expose] public section




noncomputable section
open Module IsDiscreteValuationRing
open scoped nonZeroDivisors

namespace IsDiscreteValuationRing.FiniteNorm

universe u v w w'

section Fractions
variable {A : Type u} {B : Type v} {K : Type w} {L : Type w'}
variable [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Field K] [Field L]
variable [Algebra A B] [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsFractionRing A K] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]

omit [Algebra A L] [IsScalarTower A B L] in
/-- Every fraction in an algebraic domain algebra has a denominator from the base domain. -/
theorem fractionRing_isLocalization_base [FaithfulSMul A B] [Algebra.IsAlgebraic A B] :
    IsLocalization (Algebra.algebraMapSubmonoid B A⁰) L where
  map_units r := by
    apply isUnit_iff_ne_zero.mpr
    intro h
    have h0 : (r : B) = 0 := IsFractionRing.injective B L (by simpa using h)
    obtain ⟨a, ha, he⟩ := r.property
    have hinj := FaithfulSMul.algebraMap_injective A B
    exact nonZeroDivisors.coe_ne_zero ⟨a, ha⟩ (hinj (by simpa [he] using h0))
  surj x := by
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective B x
    obtain ⟨c, d, hd, h⟩ := Algebra.IsAlgebraic.exists_smul_eq_mul A a
      (nonZeroDivisors.coe_ne_zero ⟨b, hb⟩)
    refine ⟨⟨c, ⟨algebraMap A B d, ⟨d, mem_nonZeroDivisors_of_ne_zero hd, rfl⟩⟩⟩, ?_⟩
    rw [div_mul_eq_mul_div, div_eq_iff]
    · simpa only [← map_mul, Algebra.smul_def, mul_comm] using congrArg (algebraMap B L) h
    · exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
        hb
  exists_of_eq h := by
    exact ⟨1, by simpa using IsFractionRing.injective B L h⟩

/-- Actual field norm agrees with the determinant norm after localization. -/
theorem fieldNorm_algebraMap [Module.Free A B] [Module.Finite A B] (b : B) :
    Algebra.norm K (algebraMap B L b) = algebraMap A K (Algebra.norm A b) := by
  let := FaithfulSMul.of_field_isFractionRing A B K L
  let := fractionRing_isLocalization_base (A := A) (B := B) (L := L)
  exact Algebra.norm_localization A A⁰ b

/-- The extension of fraction fields of a finite free domain algebra is finite. -/
theorem fractionRing_finite [Module.Free A B] [Module.Finite A B] :
    Module.Finite K L := by
  let := FaithfulSMul.of_field_isFractionRing A B K L
  let := fractionRing_isLocalization_base (A := A) (B := B) (L := L)
  exact Module.Finite.of_basis ((Module.Free.chooseBasis A B).localizationLocalization K A⁰ L)

/-- Localization preserves the dimension represented by a finite free basis. -/
theorem fractionRing_finrank [Module.Free A B] [Module.Finite A B] :
    Module.finrank K L = Module.finrank A B := by
  let := FaithfulSMul.of_field_isFractionRing A B K L
  let := fractionRing_isLocalization_base (A := A) (B := B) (L := L)
  let b := Module.Free.chooseBasis A B
  rw [Module.finrank_eq_card_basis (b.localizationLocalization K A⁰ L),
    Module.finrank_eq_card_basis b]

variable [IsDiscreteValuationRing A]

/-- The actual fraction-field order of the norm of a nonzero algebra element is its quotient
length. -/
theorem fieldNorm_ordFrac_integral [Module.Free A B] [Module.Finite A B]
    (b : B) (hb : b ≠ 0) :
    Ring.ordFrac A (Algebra.norm K (algebraMap B L b)) =
      WithZero.exp ((Module.length A (B ⧸ Ideal.span ({b} : Set B))).toNat : ℤ) := by
  have hnorm : Algebra.norm A b ≠ 0 := Algebra.norm_ne_zero_iff.mpr hb
  have hlen : Module.length A (B ⧸ Ideal.span ({b} : Set B)) =
      addVal A (Algebra.norm A b) := length_quotient_span_eq_addVal_norm b hb
  have hn : Ring.ord A (Algebra.norm A b) =
      ((Module.length A (B ⧸ Ideal.span ({b} : Set B))).toNat : ℕ∞) := by
    rw [Ring.ord_eq_addVal, ← hlen]
    exact (ENat.natCast_toNat (by rw [hlen, ne_eq, addVal_eq_top_iff]; exact hnorm)).symm
  rw [fieldNorm_algebraMap (A := A) (K := K) (L := L) b, Ring.ordFrac_eq_ord A hnorm]
  exact Ring.ordMonoidWithZeroHom_eq_coe A (mem_nonZeroDivisors_of_ne_zero hnorm) hn

/-- The actual fraction-field order of the norm of a fraction is a difference of quotient lengths.
-/
theorem fieldNorm_ordFrac_fraction [Module.Free A B] [Module.Finite A B]
    (a b : B) (ha : a ≠ 0) (hb : b ≠ 0) :
    Ring.ordFrac A (Algebra.norm K (algebraMap B L a / algebraMap B L b)) =
      WithZero.exp (((Module.length A (B ⧸ Ideal.span ({a} : Set B))).toNat : ℤ) -
        ((Module.length A (B ⧸ Ideal.span ({b} : Set B))).toNat : ℤ)) := by
  let := fractionRing_finite (A := A) (B := B) (K := K) (L := L)
  rw [WithZero.exp_sub, div_eq_mul_inv, map_mul, Algebra.norm_inv,
    map_mul, map_inv₀, fieldNorm_ordFrac_integral (A := A) (K := K) (L := L) a ha,
    fieldNorm_ordFrac_integral (A := A) (K := K) (L := L) b hb]
  rfl

end Fractions

section LocalLength

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [Algebra A B]

/-- The single local algebra case, with its actual residue-field extension.
This intermediate result does not replace the full semilocal inverse-image algebra. -/
theorem addVal_norm_eq_residueDegree_mul_order_of_local
    [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Module.Free A B] [Module.Finite A B] (b : B) (hb : b ≠ 0) :
    addVal A (Algebra.norm A b) =
      (Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) : ℕ∞) *
        Ring.ord B b := by
  calc
    _ = Module.length A (B ⧸ Ideal.span ({b} : Set B)) :=
      (length_quotient_span_eq_addVal_norm b hb).symm
    _ = Module.length B (B ⧸ Ideal.span ({b} : Set B)) *
        Module.length (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) :=
      IsLocalRing.length_restrictScalars A B _
    _ = _ := by rw [Module.length_eq_finrank]; exact mul_comm _ _

/-- A nonzero principal quotient of a finite free domain algebra over a DVR is Artinian. -/
theorem principalQuotient_artinian [Module.Free A B] [Module.Finite A B]
    (b : B) (hb : b ≠ 0) : IsArtinianRing (B ⧸ Ideal.span ({b} : Set B)) := by
  have h := quotient_span_finiteLength_of_finite_free (R := A) b hb
  have hart : IsArtinian A (B ⧸ Ideal.span ({b} : Set B)) :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp h).2
  exact isArtinian_of_tower A hart

end LocalLength

section Decomposition

variable (A : Type u) (C : Type v) [CommRing A] [CommRing C] [Algebra A C]

/-- A finite algebra between local rings induces the canonical local homomorphism. -/
theorem finite_local_isLocalHom [IsLocalRing A] [IsLocalRing C] [Module.Finite A C] :
    IsLocalHom (algebraMap A C) := by
  apply ((IsLocalRing.local_hom_TFAE (algebraMap A C)).out 5 1).mp
  have h : ((IsLocalRing.maximalIdeal C).under A).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal (IsLocalRing.maximalIdeal C)
  exact IsLocalRing.eq_maximalIdeal h

/-- Prime localization of an Artinian finite algebra remains finite over the base. -/
theorem artinian_localization_finite [IsArtinianRing C] [Module.Finite A C]
    (p : PrimeSpectrum C) : Module.Finite A (Localization.AtPrime p.asIdeal) :=
  Module.Finite.of_surjective
    (IsScalarTower.toAlgHom A C (Localization.AtPrime p.asIdeal)).toLinearMap
    (IsArtinianRing.localization_surjective p.asIdeal.primeCompl _)

local instance [IsArtinianRing C] [Module.Finite A C] (p : PrimeSpectrum C) :
    Module.Finite A (Localization.AtPrime p.asIdeal) := artinian_localization_finite A C p

local instance [IsLocalRing A] [IsArtinianRing C] [Module.Finite A C] (p : PrimeSpectrum C) :
    IsLocalHom (algebraMap A (Localization.AtPrime p.asIdeal)) :=
  finite_local_isLocalHom A _

variable [IsArtinianRing C] [Fintype (PrimeSpectrum C)]

/-- Length decomposes over every prime localization of an Artinian algebra. -/
theorem length_eq_sum_localizations_of_artinian :
    Module.length A C =
      ∑ p : PrimeSpectrum C, Module.length A (Localization.AtPrime p.asIdeal) := by
  exact (((PrimeSpectrum.toPiLocalizationEquiv C).restrictScalars A).toLinearEquiv.length_eq).trans
    (Module.length_pi_of_fintype _ _)

/-- Each Artinian localization contributes its local length times its actual residue degree. -/
theorem length_eq_sum_residueLengths_of_artinian [IsLocalRing A] [Module.Finite A C] :
    Module.length A C =
      ∑ p : PrimeSpectrum C,
        (Module.finrank (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) : ℕ∞) *
          Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) := by
  rw [length_eq_sum_localizations_of_artinian A C]
  apply Finset.sum_congr rfl
  intro p _
  rw [IsLocalRing.length_restrictScalars A (Localization.AtPrime p.asIdeal),
    Module.length_eq_finrank, mul_comm]

section NormSupport

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [Algebra A B]
variable [Module.Free A B] [Module.Finite A B]

/-- Determinant valuation as a sum over all supporting quotient localizations. -/
theorem addVal_norm_eq_sum_quotientLocalizations (b : B) (hb : b ≠ 0)
    [Fintype (PrimeSpectrum (B ⧸ Ideal.span ({b} : Set B)))] :
    addVal A (Algebra.norm A b) =
      ∑ p : PrimeSpectrum (B ⧸ Ideal.span ({b} : Set B)),
        Module.length A (Localization.AtPrime p.asIdeal) := by
  let := principalQuotient_artinian (A := A) b hb
  rw [← length_quotient_span_eq_addVal_norm b hb]
  exact length_eq_sum_localizations_of_artinian A (B ⧸ Ideal.span ({b} : Set B))

/-- Determinant valuation as a sum of actual quotient-local lengths and residue degrees. -/
theorem addVal_norm_eq_sum_quotientResidueLengths (b : B) (hb : b ≠ 0)
    [Fintype (PrimeSpectrum (B ⧸ Ideal.span ({b} : Set B)))] :
    letI := principalQuotient_artinian (A := A) b hb
    addVal A (Algebra.norm A b) =
      ∑ p : PrimeSpectrum (B ⧸ Ideal.span ({b} : Set B)),
        (Module.finrank (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField (Localization.AtPrime p.asIdeal)) : ℕ∞) *
          Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) := by
  let := principalQuotient_artinian (A := A) b hb
  rw [← length_quotient_span_eq_addVal_norm b hb]
  exact length_eq_sum_residueLengths_of_artinian A (B ⧸ Ideal.span ({b} : Set B))

end NormSupport

end Decomposition

section QuotientLocalizations
variable {B : Type v} [CommRing B]

/-- Localizing an actual quotient identifies it with the quotient of the corresponding
localization. -/
def localizationQuotientEquiv (I : Ideal B) (p : PrimeSpectrum (B ⧸ I)) :
    Localization.AtPrime p.asIdeal ≃ₐ[B]
      (Localization.AtPrime (p.asIdeal.under B)) ⧸
        I.map (algebraMap B (Localization.AtPrime (p.asIdeal.under B))) := by
  let q := p.asIdeal.under B
  have hM : Algebra.algebraMapSubmonoid (B ⧸ I) q.primeCompl = p.asIdeal.primeCompl :=
    Ideal.algebraMapSubmonoid_primeCompl_of_liesOver_surjective _ _ Ideal.Quotient.mk_surjective
  have : IsLocalization (Algebra.algebraMapSubmonoid (B ⧸ I) q.primeCompl)
      (Localization.AtPrime p.asIdeal) := by
    rw [hM]
    infer_instance
  exact (IsLocalization.algEquiv (Algebra.algebraMapSubmonoid (B ⧸ I) q.primeCompl)
    (Localization.AtPrime p.asIdeal)
    ((Localization.AtPrime q) ⧸ I.map (algebraMap B (Localization.AtPrime q)))).restrictScalars B

variable {A : Type u} [CommRing A] [Algebra A B]

/-- The quotient/localization comparison preserves the actual base-module length. -/
theorem quotientLocalization_length_base (I : Ideal B) (p : PrimeSpectrum (B ⧸ I)) :
    Module.length A (Localization.AtPrime p.asIdeal) =
      Module.length A ((Localization.AtPrime (p.asIdeal.under B)) ⧸
        I.map (algebraMap B (Localization.AtPrime (p.asIdeal.under B)))) :=
  ((localizationQuotientEquiv I p).restrictScalars A).toLinearEquiv.length_eq

section MaximalLocalizations
variable [IsLocalRing A] [Module.Finite A B]

/-- A maximal branch of a finite algebra over a local ring induces the actual local base map. -/
theorem localizationAtMaximal_isLocalHom (q : Ideal B) [q.IsMaximal] :
    IsLocalHom (algebraMap A (Localization.AtPrime q)) := by
  apply ((IsLocalRing.local_hom_TFAE _).out 5 1).mp
  rw [IsScalarTower.algebraMap_eq A B (Localization.AtPrime q), ← Ideal.comap_comap]
  change ((IsLocalRing.maximalIdeal (Localization.AtPrime q)).under B).under A = _
  rw [IsLocalization.AtPrime.under_maximalIdeal (Localization.AtPrime q) q]
  exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal q)

local instance (q : Ideal B) [q.IsMaximal] :
    IsLocalHom (algebraMap A (Localization.AtPrime q)) := localizationAtMaximal_isLocalHom q

/-- The branch residue field is the actual maximal-ideal quotient, compatibly with the base. -/
def maximalLocalizationResidueEquiv (q : Ideal B) [q.IsMaximal] :
    (B ⧸ q) ≃ₐ[A] IsLocalRing.ResidueField (Localization.AtPrime q) where
  __ := IsLocalization.AtPrime.equivQuotMaximalIdeal q (Localization.AtPrime q)
  commutes' a := by
    change IsLocalization.AtPrime.equivQuotMaximalIdeal q (Localization.AtPrime q)
      (Ideal.Quotient.mk q (algebraMap A B a)) = _
    rw [IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk]
    rfl

/-- Every maximal branch has a finite actual residue-field extension. -/
theorem maximalLocalization_residue_finite (q : Ideal B) [q.IsMaximal] :
    Module.Finite (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField (Localization.AtPrime q)) := by
  have : Module.Finite A (IsLocalRing.ResidueField (Localization.AtPrime q)) :=
    Module.Finite.of_surjective (maximalLocalizationResidueEquiv (A := A) q).toLinearMap
      (maximalLocalizationResidueEquiv (A := A) q).surjective
  exact Module.Finite.of_restrictScalars_finite A _ _

local instance (q : Ideal B) [q.IsMaximal] :
    Module.Finite (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField (Localization.AtPrime q)) := maximalLocalization_residue_finite q

/-- A supporting quotient-local length equals the branch order times its actual residue degree. -/
theorem quotientLocalization_length_eq_residueDegree_mul_order
    (b : B) (p : PrimeSpectrum (B ⧸ Ideal.span ({b} : Set B)))
    [(p.asIdeal.under B).IsMaximal] :
    Module.length A (Localization.AtPrime p.asIdeal) =
      (Module.finrank (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField (Localization.AtPrime (p.asIdeal.under B))) : ℕ∞) *
        Ring.ord (Localization.AtPrime (p.asIdeal.under B))
          (algebraMap B (Localization.AtPrime (p.asIdeal.under B)) b) := by
  rw [quotientLocalization_length_base (A := A), Ideal.map_span, Set.image_singleton]
  rw [IsLocalRing.length_restrictScalars A (Localization.AtPrime (p.asIdeal.under B)),
    Module.length_eq_finrank, mul_comm]
  rfl

end MaximalLocalizations

section BaseDVR
variable [IsDomain A] [IsDiscreteValuationRing A] [IsDomain B] [Module.Finite A B]

local instance (q : Ideal B) [q.IsMaximal] :
    IsLocalHom (algebraMap A (Localization.AtPrime q)) :=
  localizationAtMaximal_isLocalHom (A := A) q

local instance (q : Ideal B) [q.IsMaximal] :
    Module.Finite (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField (Localization.AtPrime q)) :=
  maximalLocalization_residue_finite (A := A) q

include A in
/-- Every prime of a nonzero principal quotient of a finite domain algebra over a DVR is a maximal
branch. -/
theorem quotientPrime_under_isMaximal (b : B) (hb : b ≠ 0)
    (p : PrimeSpectrum (B ⧸ Ideal.span ({b} : Set B))) :
    (p.asIdeal.under B).IsMaximal := by
  let q := p.asIdeal.under B
  have hbq : b ∈ q := by
    change algebraMap B (B ⧸ Ideal.span ({b} : Set B)) b ∈ p.asIdeal
    have hb0 : algebraMap B (B ⧸ Ideal.span ({b} : Set B)) b = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    rw [hb0]
    exact p.asIdeal.zero_mem
  have hba : IsAlgebraic A b := Algebra.IsAlgebraic.isAlgebraic b
  obtain ⟨a, ha, c, hc⟩ := hba.exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hb)
  have haq : a ∈ q.under A := by
    change algebraMap A B a ∈ q
    rw [hc]
    exact q.mul_mem_right c hbq
  have hne : q.under A ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at haq
    exact ha haq
  have hmax : (q.under A).IsMaximal := Ideal.isMaximal_of_isPrime_of_ne_bot (q.under A) hne
  exact Ideal.isMaximal_of_isIntegral_of_isMaximal_under q hmax

/-- The supporting quotient decomposition expressed with the actual orders on branch
localizations. -/
theorem addVal_norm_eq_sum_localOrders [Module.Free A B] (b : B) (hb : b ≠ 0)
    [Fintype (PrimeSpectrum (B ⧸ Ideal.span ({b} : Set B)))] :
    IsDiscreteValuationRing.addVal A (Algebra.norm A b) =
      ∑ p : PrimeSpectrum (B ⧸ Ideal.span ({b} : Set B)),
        letI := quotientPrime_under_isMaximal (A := A) b hb p
        (Module.finrank (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField (Localization.AtPrime (p.asIdeal.under B))) : ℕ∞) *
          Ring.ord (Localization.AtPrime (p.asIdeal.under B))
            (algebraMap B (Localization.AtPrime (p.asIdeal.under B)) b) := by
  rw [addVal_norm_eq_sum_quotientLocalizations b hb]
  apply Finset.sum_congr rfl
  intro p _
  let := quotientPrime_under_isMaximal (A := A) b hb p
  exact quotientLocalization_length_eq_residueDegree_mul_order b p

include A in
/-- All supporting maximal ideals, without selecting a single branch. -/
def quotientPrimeEquivMaximalSupport (b : B) (hb : b ≠ 0) :
    PrimeSpectrum (B ⧸ Ideal.span ({b} : Set B)) ≃
      {q : MaximalSpectrum B // b ∈ q.asIdeal} where
  toFun p := ⟨⟨p.asIdeal.under B, quotientPrime_under_isMaximal (A := A) b hb p⟩, by
    change algebraMap B (B ⧸ Ideal.span ({b} : Set B)) b ∈ p.asIdeal
    have h0 : algebraMap B (B ⧸ Ideal.span ({b} : Set B)) b = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
    rw [h0]
    exact p.asIdeal.zero_mem⟩
  invFun q := ⟨q.val.asIdeal.map (Ideal.Quotient.mk (Ideal.span ({b} : Set B))),
    Ideal.isPrime_map_quotientMk_of_isPrime (Ideal.span_le.mpr (by simpa using q.property))⟩
  left_inv p := by
    apply PrimeSpectrum.ext
    exact p.asIdeal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective
  right_inv q := by
    apply Subtype.ext
    apply MaximalSpectrum.ext
    exact Ideal.comap_map_mk (Ideal.span_le.mpr (by simpa using q.property))

include A in
omit [IsDomain B] in
/-- A finite algebra over the base DVR is semilocal. -/
theorem maximalSpectrum_finite_of_finite_algebra : Finite (MaximalSpectrum B) := by
  have hfin := Algebra.QuasiFinite.finite_primesOver (R := A) (S := B) (IsLocalRing.maximalIdeal A)
  let e : MaximalSpectrum B → (IsLocalRing.maximalIdeal A).primesOver B := fun q =>
    ⟨q.asIdeal, q.isMaximal.isPrime, ⟨(IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_under_of_isIntegral_of_isMaximal q.asIdeal)).symm⟩⟩
  have he : Function.Injective e := by
    intro q r h
    exact MaximalSpectrum.ext (congrArg Subtype.val h)
  let := hfin.to_subtype
  exact Finite.of_injective e he

/-- The determinant norm/order formula over every actual maximal branch of a finite free domain
algebra.
Nonsupporting branches contribute zero. No separability or perfectness is assumed. -/
theorem addVal_norm_eq_sum_all_maximal [Module.Free A B] [Fintype (MaximalSpectrum B)]
    (b : B) (hb : b ≠ 0) :
    IsDiscreteValuationRing.addVal A (Algebra.norm A b) =
      ∑ q : MaximalSpectrum B,
        (Module.finrank (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) : ℕ∞) *
          Ring.ord (Localization.AtPrime q.asIdeal)
            (algebraMap B (Localization.AtPrime q.asIdeal) b) := by
  classical
  let e := quotientPrimeEquivMaximalSupport (A := A) b hb
  let : Fintype (PrimeSpectrum (B ⧸ Ideal.span ({b} : Set B))) := Fintype.ofEquiv _ e.symm
  let t : MaximalSpectrum B → ℕ∞ := fun q =>
    (Module.finrank (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) : ℕ∞) *
      Ring.ord (Localization.AtPrime q.asIdeal) (algebraMap B (Localization.AtPrime q.asIdeal) b)
  have hs : IsDiscreteValuationRing.addVal A (Algebra.norm A b) =
      ∑ p : PrimeSpectrum (B ⧸ Ideal.span ({b} : Set B)), t (e p).val := by
    exact addVal_norm_eq_sum_localOrders b hb
  rw [hs, e.sum_comp (fun q => t q.val)]
  have hzero : ∑ q : {q : MaximalSpectrum B // b ∉ q.asIdeal}, t q.val = 0 := by
    apply Finset.sum_eq_zero
    intro q _
    have hu : IsUnit (algebraMap B (Localization.AtPrime q.val.asIdeal) b) :=
      IsLocalization.map_units _ (⟨b, q.property⟩ : q.val.asIdeal.primeCompl)
    dsimp [t]
    rw [Ring.ord_of_isUnit hu, mul_zero]
  have hsum := Fintype.sum_subtype_add_sum_subtype (fun q : MaximalSpectrum B => b ∈ q.asIdeal) t
  rw [hzero, add_zero] at hsum
  exact hsum

end BaseDVR

end QuotientLocalizations

section FractionOrders
variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [Algebra A B] [Module.Finite A B]

local instance (q : Ideal B) [q.IsMaximal] :
    IsLocalHom (algebraMap A (Localization.AtPrime q)) :=
  localizationAtMaximal_isLocalHom (A := A) q

local instance (q : Ideal B) [q.IsMaximal] :
    Module.Finite (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField (Localization.AtPrime q)) :=
  maximalLocalization_residue_finite (A := A) q

variable [Module.Free A B] [Fintype (MaximalSpectrum B)]

/-- The all-branch quotient-length identity in natural numbers; all summed lengths are finite. -/
theorem length_principalQuotient_toNat_eq_sum_all_maximal (b : B) (hb : b ≠ 0) :
    (Module.length A (B ⧸ Ideal.span ({b} : Set B))).toNat =
      ∑ q : MaximalSpectrum B,
        Module.finrank (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) *
          (Ring.ord (Localization.AtPrime q.asIdeal)
            (algebraMap B (Localization.AtPrime q.asIdeal) b)).toNat := by
  have hlen : Module.length A (B ⧸ Ideal.span ({b} : Set B)) = addVal A (Algebra.norm A b) :=
    length_quotient_span_eq_addVal_norm (R := A) b hb
  have h := hlen.trans (addVal_norm_eq_sum_all_maximal b hb)
  have hfinite : Module.length A (B ⧸ Ideal.span ({b} : Set B)) ≠ ⊤ := by
    rw [hlen, ne_eq, addVal_eq_top_iff]
    exact Algebra.norm_ne_zero_iff.mpr hb
  have hsumfinite := hfinite
  rw [h] at hsumfinite
  have hnat := congrArg ENat.toNat h
  rw [ENat.toNat_sum (ENat.sum_ne_top.mp hsumfinite)] at hnat
  simpa only [ENat.toNat_mul, ENat.toNat_natCast] using hnat

variable {K : Type w} {L : Type w'} [Field K] [Field L]
variable [Algebra A K] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsFractionRing A K] [IsFractionRing B L]
variable [IsScalarTower A B L] [IsScalarTower A K L]

/-- Fraction norm order as the sum of every branch's numerator and denominator length difference. -/
theorem fieldNorm_ordFrac_fraction_eq_sum_all_maximal
    (a b : B) (ha : a ≠ 0) (hb : b ≠ 0) :
    Ring.ordFrac A (Algebra.norm K (algebraMap B L a / algebraMap B L b)) =
      WithZero.exp (∑ q : MaximalSpectrum B,
        (Module.finrank (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) : ℤ) *
          (((Ring.ord (Localization.AtPrime q.asIdeal)
              (algebraMap B (Localization.AtPrime q.asIdeal) a)).toNat : ℤ) -
            ((Ring.ord (Localization.AtPrime q.asIdeal)
              (algebraMap B (Localization.AtPrime q.asIdeal) b)).toNat : ℤ))) := by
  rw [fieldNorm_ordFrac_fraction a b ha hb,
    length_principalQuotient_toNat_eq_sum_all_maximal a ha,
    length_principalQuotient_toNat_eq_sum_all_maximal b hb]
  congr 1
  simp only [Nat.cast_sum, Nat.cast_mul]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro q _
  rw [mul_sub]

omit [Fintype (MaximalSpectrum B)] [Module.Finite A B] [Module.Free A B] in
/-- The canonical map from a maximal branch localization into the actual fraction field of `B`. -/
@[instance_reducible]
def branchFractionAlgebra (q : MaximalSpectrum B) : Algebra (Localization.AtPrime q.asIdeal) L :=
  (IsLocalization.lift (S := Localization.AtPrime q.asIdeal) (g := algebraMap B L)
    (fun s : q.asIdeal.primeCompl => IsLocalization.map_units L
      (⟨s.val, q.asIdeal.primeCompl_le_nonZeroDivisors s.property⟩ : nonZeroDivisors B))).toAlgebra

omit [Fintype (MaximalSpectrum B)] [Module.Finite A B] [Module.Free A B] in
/-- The canonical branch fraction map commutes with the original map from `B`. -/
theorem branchFraction_scalarTower (q : MaximalSpectrum B) :
    letI := branchFractionAlgebra (L := L) q
    IsScalarTower B (Localization.AtPrime q.asIdeal) L := by
  let := branchFractionAlgebra (L := L) q
  apply IsScalarTower.of_algebraMap_eq
  intro b
  exact (IsLocalization.lift_eq _ b).symm

omit [Fintype (MaximalSpectrum B)] [Module.Finite A B] [Module.Free A B] in
/-- The actual fraction field of `B` is also the fraction field of every branch localization. -/
theorem branchFraction_isFractionRing (q : MaximalSpectrum B) :
    letI := branchFractionAlgebra (L := L) q
    IsFractionRing (Localization.AtPrime q.asIdeal) L := by
  let := branchFractionAlgebra (L := L) q
  let := branchFraction_scalarTower (L := L) q
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization q.asIdeal.primeCompl
    (Localization.AtPrime q.asIdeal) L

/-- Mathlib's actual fraction-field order extends the length-defined ring order on a DVR. -/
theorem ordFrac_algebraMap_eq_exp_order_toNat
    {R F : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Field F] [Algebra R F] [IsFractionRing R F] (r : R) (hr : r ≠ 0) :
    Ring.ordFrac R (algebraMap R F r) = WithZero.exp ((Ring.ord R r).toNat : ℤ) := by
  have hfinite : Ring.ord R r ≠ ⊤ := by rw [Ring.ord_eq_addVal, ne_eq, addVal_eq_top_iff]; exact hr
  rw [Ring.ordFrac_eq_ord R hr]
  exact Ring.ordMonoidWithZeroHom_eq_coe R (mem_nonZeroDivisors_of_ne_zero hr)
    (ENat.natCast_toNat hfinite).symm

omit [Fintype (MaximalSpectrum B)] in
/-- The canonical branch order of a fraction is its numerator order minus its denominator order. -/
theorem branch_ordFrac_fraction (q : MaximalSpectrum B)
    [IsDiscreteValuationRing (Localization.AtPrime q.asIdeal)]
    (a b : B) (ha : a ≠ 0) (hb : b ≠ 0) :
    letI := branchFractionAlgebra (L := L) q
    letI := branchFraction_isFractionRing (L := L) q
    Ring.ordFrac (Localization.AtPrime q.asIdeal) (algebraMap B L a / algebraMap B L b) =
      WithZero.exp (((Ring.ord (Localization.AtPrime q.asIdeal)
          (algebraMap B (Localization.AtPrime q.asIdeal) a)).toNat : ℤ) -
        ((Ring.ord (Localization.AtPrime q.asIdeal)
          (algebraMap B (Localization.AtPrime q.asIdeal) b)).toNat : ℤ)) := by
  let := branchFractionAlgebra (L := L) q
  let := branchFraction_isFractionRing (L := L) q
  let := branchFraction_scalarTower (L := L) q
  have hinj := IsLocalization.injective (Localization.AtPrime q.asIdeal)
    q.asIdeal.primeCompl_le_nonZeroDivisors
  have ha' : algebraMap B (Localization.AtPrime q.asIdeal) a ≠ 0 :=
    fun h => ha (hinj (by simpa using h))
  have hb' : algebraMap B (Localization.AtPrime q.asIdeal) b ≠ 0 :=
    fun h => hb (hinj (by simpa using h))
  rw [IsScalarTower.algebraMap_apply B (Localization.AtPrime q.asIdeal) L a,
    IsScalarTower.algebraMap_apply B (Localization.AtPrime q.asIdeal) L b,
    map_div₀, ordFrac_algebraMap_eq_exp_order_toNat _ ha',
    ordFrac_algebraMap_eq_exp_order_toNat _ hb', WithZero.exp_sub]

include K L in
omit [Module.Free A B] [Fintype (MaximalSpectrum B)] [IsFractionRing B L] in
/-- Finite domain data with compatible fraction-field maps give a free module over the base DVR. -/
theorem finiteDomain_free : Module.Free A B := by
  let := FaithfulSMul.of_field_isFractionRing A B K L
  infer_instance

omit [Module.Free A B] in
/-- The algebraic norm/order formula for all maximal branches and every actual fraction-field unit.
The base is a DVR, `B` is a finite domain algebra, and every maximal localization of `B` is a DVR.
The fraction-field algebra maps and their scalar towers are actual maps; inseparability is allowed.
This theorem does not supply the scheme realization of `B` or the geometric branch bijection. -/
theorem fieldNorm_order_eq_sum_all_maximal
    [∀ q : MaximalSpectrum B, IsDiscreteValuationRing (Localization.AtPrime q.asIdeal)]
    (z : Lˣ) :
    ((Ring.ordFrac A (Algebra.norm K (z : L))).unzeroD 1).toAdd =
      ∑ q : MaximalSpectrum B,
        letI := branchFractionAlgebra (L := L) q
        letI := branchFraction_isFractionRing (L := L) q
        (Module.finrank (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) : ℤ) *
          ((Ring.ordFrac (Localization.AtPrime q.asIdeal) (z : L)).unzeroD 1).toAdd := by
  let := finiteDomain_free (A := A) (B := B) (K := K) (L := L)
  obtain ⟨a, b, hb, hz⟩ := IsFractionRing.div_surjective B (z : L)
  have hb' : b ≠ 0 := nonZeroDivisors.coe_ne_zero ⟨b, hb⟩
  have ha : a ≠ 0 := by
    intro h
    apply Units.ne_zero z
    rw [← hz, h, map_zero, zero_div]
  have hleft : ((Ring.ordFrac A (Algebra.norm K (z : L))).unzeroD 1).toAdd =
      ∑ q : MaximalSpectrum B,
        (Module.finrank (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField (Localization.AtPrime q.asIdeal)) : ℤ) *
          (((Ring.ord (Localization.AtPrime q.asIdeal)
              (algebraMap B (Localization.AtPrime q.asIdeal) a)).toNat : ℤ) -
            ((Ring.ord (Localization.AtPrime q.asIdeal)
              (algebraMap B (Localization.AtPrime q.asIdeal) b)).toNat : ℤ)) := by
    rw [← hz, fieldNorm_ordFrac_fraction_eq_sum_all_maximal a b ha hb']
    simp [WithZero.exp]
  rw [hleft]
  apply Finset.sum_congr rfl
  intro q _
  congr 1
  let := branchFractionAlgebra (L := L) q
  let := branchFraction_isFractionRing (L := L) q
  have h := branch_ordFrac_fraction (L := L) q a b ha hb'
  rw [hz] at h
  rw [h]
  simp [WithZero.exp]

end FractionOrders

end IsDiscreteValuationRing.FiniteNorm

/- Migration source: R5Lab/Aglib/RingTheory/DiscreteValuationRing/FiniteNorm.lean
Frozen packet R5 f8a3314ddecffcada2ec721d26d56a937bed9690.
SHA-256 d60cdee96f4034ff733ce436e1a17ac2a4b7e51e6ec53aa55dbd8a847ca2a6ff.
Native names and imports replace source wrappers; stated conditions and maps are retained. -/
