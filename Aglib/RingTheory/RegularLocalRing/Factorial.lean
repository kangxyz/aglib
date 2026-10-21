/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Ideal.RegularPrincipal
public import Aglib.RingTheory.RegularLocalRing.PrimeLocalization
public import Aglib.RingTheory.RegularLocalRing.PrincipalLocalization
public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.LocalProperties.Projective
public import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Factoriality of regular local rings

Dimension induction proves factoriality without a dimension bound. Inverting
a prime parameter leaves only local rings of smaller dimension. A height-one
prime on that localization is therefore projective. The original finite
ideal supplies stable freeness of its scalar extension, and rank-one
cancellation makes the localized ideal principal. The native prime-element
localization theorem descends principality to the original ring.
-/

@[expose] public section

noncomputable section

universe u

open IsLocalRing Module

private theorem projective_heightOne_of_factorial_localizations
    {S : Type u} [CommRing S] [IsDomain S] [IsNoetherianRing S]
    (J : Ideal S) [J.IsPrime] (hJ : J.height = 1)
    (hlocal : ∀ (Q : Ideal S) [Q.IsMaximal],
      UniqueFactorizationMonoid (Localization.AtPrime Q)) :
    Module.Projective S J := by
  classical
  have : Module.FinitePresentation S J := Module.finitePresentation_of_finite S J
  apply Module.projective_of_localization_maximal
  intro Q hQ
  let T := Localization.AtPrime Q
  let : UniqueFactorizationMonoid T := hlocal Q
  have hp : (J.map (algebraMap S T)).IsPrincipal := by
    by_cases hle : J ≤ Q
    · have : (J.map (algebraMap S T)).IsPrime :=
        Ideal.isPrime_map_of_isLocalizationAtPrime Q hle
      have hdisj : Disjoint (Q.primeCompl : Set S) (J : Set S) := by
        rw [Set.disjoint_left]
        intro z hz hzJ
        exact hz (hle hzJ)
      exact UniqueFactorizationMonoid.isPrincipal_of_height_eq_one
        ((IsLocalization.height_map_of_disjoint Q.primeCompl J hdisj).trans hJ)
    · have htop : J.map (algebraMap S T) = ⊤ := by
        obtain ⟨z, hzJ, hzQ⟩ := Set.not_subset.mp hle
        exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hzJ)
          (IsLocalization.map_units T (⟨z, hzQ⟩ : Q.primeCompl))
      rw [htop]
      infer_instance
  let J' : Ideal T := J.localized' T Q.primeCompl (Algebra.linearMap S T)
  have hJ' : J' = J.map (algebraMap S T) := by
    change J.localized' T Q.primeCompl (Algebra.linearMap S T) = J.map (algebraMap S T)
    rw [Ideal.map, Ideal.span, Submodule.localized'_eq_span, Algebra.coe_linearMap]
  have : J'.IsPrincipal := hJ'.symm ▸ hp
  have hne : J' ≠ ⊥ := by
    intro hz
    have hi : Function.Injective (algebraMap S T) :=
      IsLocalization.injective T Q.primeCompl_le_nonZeroDivisors
    exact (J.ne_bot_of_height_eq_one hJ)
      ((Ideal.map_eq_bot_iff_of_injective hi).mp (hJ'.symm.trans hz))
  let a := Submodule.IsPrincipal.generator J'
  have ha : J' = Ideal.span {a} :=
    (Submodule.IsPrincipal.span_singleton_generator J').symm
  have ha0 : a ≠ 0 := by
    intro hzero
    exact hne (by rw [ha, hzero, Ideal.span_singleton_zero])
  have hareg : IsSMulRegular T a :=
    IsSMulRegular.of_right_eq_zero_of_smul fun y hy =>
      (mul_eq_zero.mp hy).resolve_left ha0
  have : Module.Free T J' :=
    Module.Free.of_basis (Ideal.regularPrincipalIdealBasis J' a hareg ha)
  let e : LocalizedModule Q.primeCompl J ≃ₗ[T] J' :=
    (IsLocalizedModule.linearEquiv Q.primeCompl
      (LocalizedModule.mkLinearMap Q.primeCompl J)
      (J.toLocalized' T Q.primeCompl (Algebra.linearMap S T))).extendScalarsOfIsLocalization
        Q.primeCompl T
  exact Module.Projective.of_equiv e.symm

namespace IsRegularLocalRing

/-- A regular local ring of dimension `d` is a unique factorization domain.
The dimension is an induction index, with no upper bound imposed. -/
theorem uniqueFactorizationMonoid_of_dimension
    (d : ℕ) (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (hd : ringKrullDim R = (d : ℕ)) : UniqueFactorizationMonoid R := by
  induction d using Nat.strong_induction_on generalizing R with
  | h d ih =>
    cases d with
    | zero =>
      let := (isField_of_regularLocal_dimension_zero R (by simpa using hd)).toField
      infer_instance
    | succ d =>
      let : IsDomain R := isDomain_of_regularLocal R
      obtain ⟨x, hxm, hxreg, hquot, _⟩ := exists_regular_parameter R d hd
      have hx0 : x ≠ 0 := by
        intro hzero
        exact zero_ne_one (hxreg (by simp [hzero]))
      have : IsRegularLocalRing (R ⧸ Ideal.span {x}) := hquot
      have hprimeIdeal : (Ideal.span {x}).IsPrime :=
        (Ideal.Quotient.isDomain_iff_prime _).mp
          (isDomain_of_regularLocal (R ⧸ Ideal.span {x}))
      have hxprime : Prime x := (Ideal.span_singleton_prime hx0).mp hprimeIdeal
      let S := Localization.Away x
      have : IsDomain S := IsLocalization.Away.isDomain S hx0
      have hlocal : ∀ (Q : Ideal S) [Q.IsMaximal],
          UniqueFactorizationMonoid (Localization.AtPrime Q) := by
        intro Q hQ
        let q := Q.comap (algebraMap R S)
        have : q.IsPrime := Ideal.comap_isPrime _ Q
        let T := Localization.AtPrime Q
        have : IsLocalization.AtPrime T q :=
          IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
            (Submonoid.powers x) T Q
        have : IsRegularLocalRing T := of_isLocalizationAtPrime R q T
        have hxq : x ∉ q := by
          intro hxq
          exact hQ.ne_top (Q.eq_top_of_isUnit_mem hxq
            (IsLocalization.Away.algebraMap_isUnit x))
        have hqm : q ≠ maximalIdeal R := by
          intro he
          rw [he] at hxq
          exact hxq hxm
        have hlt : q < maximalIdeal R :=
          lt_of_le_of_ne (le_maximalIdeal (inferInstance : q.IsPrime).ne_top) hqm
        have hheight : q.height < (maximalIdeal R).height :=
          Ideal.height_strict_mono_of_isPrime_of_isPrime hlt
        have hdim : ringKrullDim T < ringKrullDim R := by
          rw [IsLocalization.AtPrime.ringKrullDim_eq_height q T,
            ← maximalIdeal_height_eq_ringKrullDim (R := R)]
          exact_mod_cast hheight
        let k := (maximalIdeal T).spanFinrank
        have hkdim : ringKrullDim T = (k : ℕ) := spanFinrank_maximalIdeal.symm
        have hk : k < d + 1 := by
          rw [hkdim, hd] at hdim
          exact_mod_cast hdim
        exact ih k hk T hkdim
      apply UniqueFactorizationMonoid.of_forall_isPrincipal_of_height_eq_one
      intro p hp hpheight
      by_cases hxp : x ∈ p
      · exact ⟨x, p.eq_span_singleton_of_height_eq_one hpheight hxp hxprime⟩
      · have hdisj := (Ideal.disjoint_powers_iff_notMem_of_isPrime x).mpr hxp
        let J := p.map (algebraMap R S)
        have : J.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
          (Submonoid.powers x) S p hp hdisj
        have hJ : J.height = 1 :=
          (IsLocalization.height_map_of_disjoint (Submonoid.powers x) p hdisj).trans hpheight
        have : Module.Projective S J := projective_heightOne_of_factorial_localizations J hJ hlocal
        exact p.isPrincipal_of_isPrincipal_localizationAway_of_prime hxprime hxp
          (isPrincipal_map_of_projective_localization R (Submonoid.powers x) S p)

/-- Every regular local ring is factorial, with domainness derived internally
from regularity and without any bound on dimension. -/
@[stacks 0AG0]
theorem uniqueFactorizationMonoid_of_regularLocal
    (R : Type u) [CommRing R] [IsRegularLocalRing R] : UniqueFactorizationMonoid R :=
  uniqueFactorizationMonoid_of_dimension (maximalIdeal R).spanFinrank R
    spanFinrank_maximalIdeal.symm

/-- Every actual height-one prime ideal of a regular local ring is principal. -/
theorem isPrincipal_of_height_eq_one
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1) : p.IsPrincipal := by
  let : IsDomain R := isDomain_of_regularLocal R
  let : UniqueFactorizationMonoid R := uniqueFactorizationMonoid_of_regularLocal R
  exact UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hp

/-- A height-one prime in a regular local ring has a singleton basis as the
actual ideal module in every dimension. -/
def heightOneIdealBasis
    (R : Type u) [CommRing R] [IsRegularLocalRing R]
    (p : Ideal R) [p.IsPrime] (hp : p.height = 1) : Basis PUnit.{u + 1} R p := by
  let : IsDomain R := isDomain_of_regularLocal R
  let : p.IsPrincipal := isPrincipal_of_height_eq_one R p hp
  let a := Submodule.IsPrincipal.generator p
  have ha : p = Ideal.span {a} := (Submodule.IsPrincipal.span_singleton_generator p).symm
  have ha0 : a ≠ 0 := by
    intro hzero
    exact (Ideal.ne_bot_of_height_eq_one hp) (by rw [ha, hzero, Ideal.span_singleton_zero])
  exact Ideal.regularPrincipalIdealBasis p a
    (isSMulRegular_of_regularLocal_ne_zero R a ha0) ha

end IsRegularLocalRing
