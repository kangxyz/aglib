/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.Normalization
public import Aglib.RingTheory.IntegralClosure.FiniteLocalization
public import Aglib.RingTheory.IntegralClosure.RationalAdjunction
public import Aglib.RingTheory.Nagata.Completion
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Aglib.RingTheory.IntegralClosure.FiniteOverNormal
public import Aglib.RingTheory.Nagata.Finite
public import Aglib.RingTheory.Nagata.Localization
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# Finite normalization for rational adjunction over a normal surface ring

The nonzero-generator local branch follows from associated DVRs and reduced
completion. A monic residue relation, obtained after one coefficient
localization, reduces the general local case through the actual finite
birational inclusion R[f(x)] into R[x] and a second localization. The final
normal-principal-open theorem uses the original denominator, field and
maximal-local fraction maps. FiniteTypeSurface is the stability consumer.
-/

@[expose] public noncomputable section

open IsLocalRing Polynomial Module.associatedPrimes

universe u

namespace AdicCompletion

variable (R K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- The actual maximal-local completion of a rational adjunction is reduced
when its generator is nonzero and lies in the selected maximal ideal. -/
theorem isReduced_atMaximal_adjoin_singleton_of_mem
    (hR : IsNagataRing.{u, 0} R) (hdim : ringKrullDim R ≤ 2)
    (x : K) (hx : x ≠ 0)
    (m : Ideal (Algebra.adjoin R ({x} : Set K))) [m.IsMaximal]
    (hxm : Algebra.adjoinSingletonGenerator R x ∈ m) :
    IsReduced (AdicCompletion
      (maximalIdeal (Localization.AtPrime m)) (Localization.AtPrime m)) := by
  let : IsNoetherianRing R := hR.isNoetherianRing
  let S := Algebra.adjoin R ({x} : Set K)
  let z : S := Algebra.adjoinSingletonGenerator R x
  let T := Localization.AtPrime m
  let : Algebra.FiniteType R S := Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton x)
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  let : IsNoetherianRing T := IsLocalization.isNoetherianRing m.primeCompl T inferInstance
  let t : T := algebraMap S T z
  have hz : z ≠ 0 := by
    intro h
    exact hx (congrArg (fun s : S => (s : K)) h)
  have ht : t ≠ 0 := by
    intro h
    apply hz
    apply IsLocalization.injective T m.primeCompl_le_nonZeroDivisors
    exact h.trans (_root_.map_zero (algebraMap S T)).symm
  have htm : t ∈ maximalIdeal T :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff T m z).mpr hxm
  have hdimS : ringKrullDim S ≤ 2 :=
    Algebra.ringKrullDim_adjoin_singleton_le_two_of_isFractionRing R x hdim
  have hdimT : ringKrullDim T ≤ 2 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height m T]
    exact m.height_le_ringKrullDim_of_isPrime.trans hdimS
  have hcontract (P : Ideal T) [P.IsPrime]
      (hP : IsAssociatedPrime P (T ⧸ Ideal.span {t})) :
      IsAssociatedPrime (P.comap (algebraMap S T)) (S ⧸ Ideal.span {z}) := by
    let J : Submodule S S := Ideal.span {z}
    let f : S →ₗ[S] T := Algebra.linearMap S T
    have hJ : J.localized' T m.primeCompl f = Ideal.span {t} := by
      change (Submodule.span S {z}).localized' T m.primeCompl f = Ideal.span {t}
      rw [Submodule.localized'_span]
      simp only [Set.image_singleton]
      rfl
    have hP' : IsAssociatedPrime P (T ⧸ J.localized' T m.primeCompl f) := by
      rw [hJ]
      exact hP
    have he :=
      preimage_comap_associatedPrimes_eq_associatedPrimes_of_isLocalizedModule
        m.primeCompl T (J.toLocalizedQuotient' T m.primeCompl f)
    change P ∈ (Ideal.comap (algebraMap S T)) ⁻¹' (_root_.associatedPrimes S (S ⧸ J))
    rw [he]
    exact hP'
  apply isReduced_of_associated_dvr_quotients T t htm ht
  · intro P hP hass
    let q : Ideal S := P.comap (algebraMap S T)
    let : IsDiscreteValuationRing (Localization.AtPrime q) :=
      Algebra.isDiscreteValuationRing_atPrime_adjoin_singleton R x hx q
        (hcontract P hass)
    exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
      (IsLocalization.localizationLocalizationAtPrimeIsoLocalization m.primeCompl P)
  · intro P hP hass
    let q : Ideal S := P.comap (algebraMap S T)
    let D := S ⧸ q
    have hzq : z ∈ q := (hcontract P hass).mem_of_quotient_span_singleton
    let : Module.Finite R D := Module.Finite.of_surjective (Algebra.linearMap R D)
      (Algebra.adjoinSingleton_quotient_algebraMap_surjective R x q hzq)
    have hD : IsNagataRing.{u, 0} D := hR.of_finite
    let : Algebra D (T ⧸ P) := inferInstance
    let M : Submonoid D := Algebra.algebraMapSubmonoid D m.primeCompl
    let : IsLocalization M (T ⧸ P) :=
      IsLocalization.of_surjective m.primeCompl T
        (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
        (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective rfl (by
          rw [Ideal.mk_ker, Ideal.mk_ker]
          exact (IsLocalization.map_under m.primeCompl T P).ge)
    have hQ : IsNagataRing.{u, 0} (T ⧸ P) := hD.of_isLocalization M
    let : IsLocalRing (T ⧸ P) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
    have hdimQ : ringKrullDim (T ⧸ P) ≤ 1 := by
      apply ENat.WithBot.add_le_add_one_right_iff.mp
      have hdrop := ringKrullDim_succ_le_of_surjective (Ideal.Quotient.mk P)
        Ideal.Quotient.mk_surjective (r := t)
        (mem_nonZeroDivisors_iff_ne_zero.mpr ht)
        (Ideal.Quotient.eq_zero_iff_mem.mpr hass.mem_of_quotient_span_singleton)
      convert hdrop.trans hdimT using 1
      norm_num
    exact hQ.isReduced_completion_of_dimLE_one hdimQ

end AdicCompletion

namespace integralClosure

variable (R K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Finite normalization of the actual selected local ring, in the original
fraction field with the original localization lift as coefficient action. -/
theorem finite_atMaximal_adjoin_singleton_of_mem
    (hR : IsNagataRing.{u, 0} R) (hdim : ringKrullDim R ≤ 2)
    (x : K) (hx : x ≠ 0)
    (m : Ideal (Algebra.adjoin R ({x} : Set K))) [m.IsMaximal]
    (hxm : Algebra.adjoinSingletonGenerator R x ∈ m) :
    letI : IsFractionRing (Algebra.adjoin R ({x} : Set K)) K :=
      Algebra.isFractionRing_adjoin_singleton R x
    letI : Algebra (Localization.AtPrime m) K :=
      (atPrimeFractionMap (Algebra.adjoin R ({x} : Set K)) K m).toRingHom.toAlgebra
    Module.Finite (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) K) := by
  let : IsNoetherianRing R := hR.isNoetherianRing
  let S := Algebra.adjoin R ({x} : Set K)
  let T := Localization.AtPrime m
  let : IsFractionRing S K := Algebra.isFractionRing_adjoin_singleton R x
  let φ : T →ₐ[S] K := atPrimeFractionMap S K m
  let : Algebra T K := φ.toRingHom.toAlgebra
  let : IsScalarTower S T K := IsScalarTower.of_algHom φ
  let : IsFractionRing T K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization m.primeCompl T K
  let : Algebra.FiniteType R S := Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton x)
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  let : IsNoetherianRing T := IsLocalization.isNoetherianRing m.primeCompl T inferInstance
  have hdimS : ringKrullDim S ≤ 2 :=
    Algebra.ringKrullDim_adjoin_singleton_le_two_of_isFractionRing R x hdim
  let : Ring.KrullDimLE 2 T := Ring.krullDimLE_iff.mpr (by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height m T]
    exact m.height_le_ringKrullDim_of_isPrime.trans hdimS)
  change Module.Finite T (integralClosure T K)
  exact finite_of_isReduced_completion_of_dimLE_two T
    (AdicCompletion.isReduced_atMaximal_adjoin_singleton_of_mem R K hR hdim x hx m hxm) K

end integralClosure

namespace integralClosure


/-- Local N-1 ascent for a finite integral birational map, with the original
localization actions on the common fraction field. -/
theorem finite_atPrime_of_finite_birational
    (R S K : Type u) [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S]
    [Field K] [Algebra R K] [IsFractionRing R K] [Algebra S K] [IsFractionRing S K]
    [IsScalarTower R S K]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hpq : p = q.comap (algebraMap R S))
    (hfinite :
      letI : Algebra (Localization.AtPrime p) K :=
        (atPrimeFractionMap R K p).toRingHom.toAlgebra
      Module.Finite (Localization.AtPrime p) (integralClosure (Localization.AtPrime p) K)) :
    letI : Algebra (Localization.AtPrime q) K :=
      (atPrimeFractionMap S K q).toRingHom.toAlgebra
    Module.Finite (Localization.AtPrime q) (integralClosure (Localization.AtPrime q) K) := by
  let A := Localization.AtPrime p
  let M : Submonoid S := Algebra.algebraMapSubmonoid S p.primeCompl
  let T := Localization M
  let U := Localization.AtPrime q
  have hMN : M ≤ q.primeCompl := by
    rintro s ⟨r, hr, rfl⟩
    change algebraMap R S r ∉ q
    change r ∉ p at hr
    rw [hpq] at hr
    exact hr
  let κA : A →ₐ[R] K := atPrimeFractionMap R K p
  let : Algebra A K := κA.toRingHom.toAlgebra
  let : IsScalarTower R A K := IsScalarTower.of_algHom κA
  let : IsFractionRing A K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization p.primeCompl A K
  let : IsScalarTower R S T := inferInstance
  let : IsScalarTower R A T := inferInstance
  let α : A →ₐ[R] T := IsScalarTower.toAlgHom R A T
  let : Module.Finite A T := Module.Finite.of_isLocalization R S p.primeCompl
  let ρ : T →ₐ[S] K := IsLocalization.liftAlgHom (M := M) (f := Algebra.ofId S K)
    (fun s => IsLocalization.map_units K
      ⟨s.val, q.primeCompl_le_nonZeroDivisors (hMN s.property)⟩)
  let : Algebra T K := ρ.toRingHom.toAlgebra
  let : IsScalarTower S T K := IsScalarTower.of_algHom ρ
  let : IsScalarTower R T K := IsScalarTower.to₁₃₄ R S T K
  have hρ : (ρ.restrictScalars R).comp α = κA :=
    (IsLocalization.algHom_subsingleton p.primeCompl).elim _ _
  let : IsScalarTower A T K := IsScalarTower.of_algebraMap_eq fun a =>
    (AlgHom.congr_fun hρ a).symm
  let : Module.Finite A (integralClosure A K) := hfinite
  let : Algebra.IsIntegral A T := inferInstance
  let : Module.Finite A (integralClosure T K) :=
    Module.Finite.equiv (integralClosure.equivOfIntegral A T K).symm.toLinearEquiv
  let : Module.Finite T (integralClosure T K) :=
    Module.Finite.of_restrictScalars_finite A T _
  let δ : T →ₐ[S] U := IsLocalization.liftAlgHom (M := M) (f := Algebra.ofId S U)
    (fun s => IsLocalization.map_units U ⟨s.val, hMN s.property⟩)
  let : Algebra T U := δ.toRingHom.toAlgebra
  let : IsScalarTower S T U := IsScalarTower.of_algHom δ
  let κU : U →ₐ[S] K := atPrimeFractionMap S K q
  let : Algebra U K := κU.toRingHom.toAlgebra
  let : IsScalarTower S U K := IsScalarTower.of_algHom κU
  have hδ : κU.comp δ = ρ :=
    (IsLocalization.algHom_subsingleton M).elim _ _
  let : IsScalarTower T U K := IsScalarTower.of_algebraMap_eq fun t =>
    (AlgHom.congr_fun hδ t).symm
  let H : Submonoid T := q.primeCompl.map (algebraMap S T)
  let : IsLocalization H U :=
    IsLocalization.isLocalization_of_submonoid_le (S := T) (T := U) M q.primeCompl hMN
  let l : integralClosure T K →ₗ[T] integralClosure U K :=
    (scalarExtensionHom T U K).toLinearMap
  let : IsLocalizedModule H l := scalarExtensionHom_isLocalizedModule T U K H
  change Module.Finite U (integralClosure U K)
  exact Module.Finite.of_isLocalizedModule H l

end integralClosure

namespace integralClosure


/-- Prime localization after a localization returns the original local ring;
finiteness of its normalization retains the original supplied field action. -/
theorem finite_atPrime_of_isLocalization
    (R S K : Type u) [CommRing R] [IsDomain R]
    [CommRing S] [IsDomain S] [Algebra R S]
    [Field K] [Algebra R K] [IsFractionRing R K] [Algebra S K] [IsFractionRing S K]
    [IsScalarTower R S K] (M : Submonoid R) [IsLocalization M S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hpq : p = q.comap (algebraMap R S))
    (hfinite :
      letI : Algebra (Localization.AtPrime q) K :=
        (atPrimeFractionMap S K q).toRingHom.toAlgebra
      Module.Finite (Localization.AtPrime q) (integralClosure (Localization.AtPrime q) K)) :
    letI : Algebra (Localization.AtPrime p) K :=
      (atPrimeFractionMap R K p).toRingHom.toAlgebra
    Module.Finite (Localization.AtPrime p) (integralClosure (Localization.AtPrime p) K) := by
  let A := Localization.AtPrime p
  let B := Localization.AtPrime q
  let : IsScalarTower R S B := inferInstance
  let : IsLocalization p.primeCompl B := by
    have hM : p.primeCompl = (q.comap (algebraMap R S)).primeCompl := by
      ext r
      change r ∉ p ↔ r ∉ q.comap (algebraMap R S)
      rw [hpq]
    exact Eq.mp (congrArg (fun N : Submonoid R => IsLocalization N B) hM.symm)
      (IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (S := S) M B q)
  let e : A ≃ₐ[R] B := IsLocalization.algEquiv p.primeCompl A B
  let : Algebra A B := e.toRingHom.toAlgebra
  let : IsScalarTower R A B := IsScalarTower.of_algHom e.toAlgHom
  let κA : A →ₐ[R] K := atPrimeFractionMap R K p
  let : Algebra A K := κA.toRingHom.toAlgebra
  let : IsScalarTower R A K := IsScalarTower.of_algHom κA
  let κB : B →ₐ[S] K := atPrimeFractionMap S K q
  let : Algebra B K := κB.toRingHom.toAlgebra
  let : IsScalarTower S B K := IsScalarTower.of_algHom κB
  let : IsScalarTower R B K := IsScalarTower.to₁₃₄ R S B K
  have he : (κB.restrictScalars R).comp e.toAlgHom = κA :=
    (IsLocalization.algHom_subsingleton p.primeCompl).elim _ _
  let : IsScalarTower A B K := IsScalarTower.of_algebraMap_eq fun a =>
    (AlgHom.congr_fun he a).symm
  let : Module.Finite A B := RingHom.Finite.of_surjective e.toRingHom e.surjective
  let : Algebra.IsIntegral A B := inferInstance
  let : Module.Finite B (integralClosure B K) := hfinite
  let : Module.Finite A (integralClosure B K) := Module.Finite.trans B _
  change Module.Finite A (integralClosure A K)
  exact Module.Finite.equiv (equivOfIntegral A B K).toLinearEquiv

end integralClosure

namespace integralClosure


variable (R K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- A monic residue relation reduces the original maximal local ring to
the nonzero-generator local case through a finite birational algebra and
then a second localization. -/
theorem finite_atMaximal_adjoin_singleton_of_monic
    (hR : IsNagataRing.{u, 0} R) (hdim : ringKrullDim R ≤ 2)
    (x : K) (m : Ideal (Algebra.adjoin R ({x} : Set K))) [m.IsMaximal]
    (f : R[X]) (hf : f.Monic)
    (hfm : aeval (Algebra.adjoinSingletonGenerator R x) f ∈ m) :
    letI : IsFractionRing (Algebra.adjoin R ({x} : Set K)) K :=
      Algebra.isFractionRing_adjoin_singleton R x
    letI : Algebra (Localization.AtPrime m) K :=
      (atPrimeFractionMap (Algebra.adjoin R ({x} : Set K)) K m).toRingHom.toAlgebra
    Module.Finite (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) K) := by
  let : IsNoetherianRing R := hR.isNoetherianRing
  let S := Algebra.adjoin R ({x} : Set K)
  let : Algebra.FiniteType R S := Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton x)
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  let : IsFractionRing S K := Algebra.isFractionRing_adjoin_singleton R x
  let u : K := aeval x f
  by_cases hu : u = 0
  · have hx : IsIntegral R x := ⟨f, hf, hu⟩
    let : Module.Finite R S := Algebra.finite_adjoin_simple_of_isIntegral hx
    have hS : IsNagataRing.{u, 0} S := hR.of_finite
    let U := Localization.AtPrime m
    let κ : U →ₐ[S] K := atPrimeFractionMap S K m
    let : Algebra U K := κ.toRingHom.toAlgebra
    let : IsScalarTower S U K := IsScalarTower.of_algHom κ
    let : IsFractionRing U K :=
      IsFractionRing.isFractionRing_of_isDomain_of_isLocalization m.primeCompl U K
    have hU : IsNagataRing.{u, 0} U := hS.of_isLocalization m.primeCompl
    change Module.Finite U (integralClosure U K)
    exact hU.isJapaneseRing.finite_integralClosure_of_isFractionRing K K
  · have hdeg : 0 < f.natDegree := hf.natDegree_pos.mpr (by
      intro hf1
      have h1 : (1 : S) ∈ m := by simpa only [hf1, map_one] using hfm
      exact (show m.IsPrime from inferInstance).ne_top ((Ideal.eq_top_iff_one m).mpr h1))
    let B := Algebra.adjoin R ({u} : Set K)
    let i : B →ₐ[R] S := Algebra.polynomialValueInclusion R x f
    let : Algebra B S := i.toRingHom.toAlgebra
    let : IsScalarTower R B S := IsScalarTower.of_algHom i
    let : IsScalarTower B S K := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let : Module.Finite B S := Algebra.finite_adjoin_singleton_over_polynomial_value
      R x f hf hdeg
    let : Algebra.IsIntegral B S := inferInstance
    let : Algebra.FiniteType R B := Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton u)
    let : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
    let : IsFractionRing B K := Algebra.isFractionRing_adjoin_singleton R u
    let n : Ideal B := m.comap (algebraMap B S)
    let : n.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal m
    have hun : Algebra.adjoinSingletonGenerator R u ∈ n := by
      have he : i (Algebra.adjoinSingletonGenerator R u) =
          aeval (Algebra.adjoinSingletonGenerator R x) f := by
        apply Subtype.ext
        change aeval x f = (aeval (Algebra.adjoinSingletonGenerator R x) f : K)
        simp only [Algebra.adjoinSingletonGenerator, Polynomial.coe_aeval_mk_apply]
      change i (Algebra.adjoinSingletonGenerator R u) ∈ m
      rw [he]
      exact hfm
    exact finite_atPrime_of_finite_birational B S K n m rfl
      (finite_atMaximal_adjoin_singleton_of_mem R K hR hdim u hu n hun)

end integralClosure

namespace integralClosure


variable (R K : Type u) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- Every maximal localization of an actual rational adjunction over a
normal Nagata surface ring has finite normalization in the supplied field. -/
theorem finite_atMaximal_adjoin_singleton_of_dimLE_two
    (hR : IsNagataRing.{u, 0} R) (hdim : ringKrullDim R ≤ 2)
    (x : K) (m : Ideal (Algebra.adjoin R ({x} : Set K))) [m.IsMaximal] :
    letI : IsFractionRing (Algebra.adjoin R ({x} : Set K)) K :=
      Algebra.isFractionRing_adjoin_singleton R x
    letI : Algebra (Localization.AtPrime m) K :=
      (atPrimeFractionMap (Algebra.adjoin R ({x} : Set K)) K m).toRingHom.toAlgebra
    Module.Finite (Localization.AtPrime m) (integralClosure (Localization.AtPrime m) K) := by
  let : IsNoetherianRing R := hR.isNoetherianRing
  let S := Algebra.adjoin R ({x} : Set K)
  let : Algebra.FiniteType R S := Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton x)
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  let : IsFractionRing S K := Algebra.isFractionRing_adjoin_singleton R x
  obtain ⟨f, hfm, hc⟩ := Algebra.exists_aeval_mem_leadingCoeff_not_mem R K x m
  let c : R := f.leadingCoeff
  have hc0 : c ≠ 0 := by
    intro h
    apply hc
    change c ∈ m.comap (algebraMap R S)
    rw [h]
    exact (m.comap (algebraMap R S)).zero_mem
  have hcK : algebraMap R K c ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hc0
  let A := Localization.Away c
  let κA : A →ₐ[R] K := IsLocalization.Away.liftAlgHom c
    (f := Algebra.ofId R K) (IsUnit.mk0 _ hcK)
  let : Algebra A K := κA.toRingHom.toAlgebra
  let : IsScalarTower R A K := IsScalarTower.of_algHom κA
  let : IsDomain A := Localization.Away.isDomain hc0
  let : IsFractionRing A K :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers c) A K
  have hM : Submonoid.powers c ≤ nonZeroDivisors R :=
    powers_le_nonZeroDivisors_of_noZeroDivisors hc0
  let : IsIntegrallyClosed A := isIntegrallyClosed_of_isLocalization A (Submonoid.powers c) hM
  have hA : IsNagataRing.{u, 0} A := hR.of_isLocalization (Submonoid.powers c)
  let : IsNoetherianRing A := hA.isNoetherianRing
  have hdimA : ringKrullDim A ≤ 2 :=
    (IsLocalization.ringKrullDim_le R A (Submonoid.powers c)).trans hdim
  let T := Algebra.adjoin A ({x} : Set K)
  let i : S →ₐ[R] T := Algebra.adjoinSingletonScalarExtension R A x
  let : Algebra S T := Algebra.adjoinSingletonScalarExtensionAlgebra R A x
  let : IsScalarTower R S T := IsScalarTower.of_algHom i
  let : IsScalarTower S T K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let M : Submonoid S := Algebra.algebraMapSubmonoid S (Submonoid.powers c)
  let : IsLocalization M T := Algebra.isLocalization_adjoin_singleton R A (Submonoid.powers c) x
  let : IsFractionRing T K := Algebra.isFractionRing_adjoin_singleton A x
  let : Algebra.FiniteType A T := Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton x)
  let : IsNoetherianRing T := Algebra.FiniteType.isNoetherianRing A T
  have hMm : M ≤ m.primeCompl := by
    rintro _ ⟨r, ⟨n, rfl⟩, rfl⟩
    change algebraMap R S (c ^ n) ∉ m
    rw [map_pow]
    intro h
    exact hc ((show m.IsPrime from inferInstance).mem_of_pow_mem n h)
  have hdis : Disjoint (M : Set S) (m : Set S) :=
    Set.disjoint_left.mpr fun _ hs hm => hMm hs hm
  let q : Ideal T := m.map (algebraMap S T)
  let : q.IsMaximal := IsLocalization.isMaximal_of_isMaximal_disjoint M T m hdis
  have hmq : m = q.comap (algebraMap S T) :=
    (IsLocalization.under_map_of_isPrime_disjoint M T
      (show m.IsPrime from inferInstance) hdis).symm
  let g : A[X] := f.map (algebraMap R A) * C (IsLocalization.Away.invSelf c)
  have hg : g.Monic := by
    apply Polynomial.monic_mul_C_of_leadingCoeff_mul_eq_one
    rw [Polynomial.leadingCoeff_map_of_injective (IsLocalization.injective A hM)]
    exact IsLocalization.Away.mul_invSelf c
  have hfq : aeval (Algebra.adjoinSingletonGenerator A x) (f.map (algebraMap R A)) ∈ q := by
    have he : i (aeval (Algebra.adjoinSingletonGenerator R x) f) =
        aeval (Algebra.adjoinSingletonGenerator A x) (f.map (algebraMap R A)) := by
      calc
        i (aeval (Algebra.adjoinSingletonGenerator R x) f) =
            aeval (i (Algebra.adjoinSingletonGenerator R x)) f :=
          (Polynomial.aeval_algHom_apply i (Algebra.adjoinSingletonGenerator R x) f).symm
        _ = aeval (Algebra.adjoinSingletonGenerator A x) f := rfl
        _ = aeval (Algebra.adjoinSingletonGenerator A x) (f.map (algebraMap R A)) :=
          (Polynomial.aeval_map_algebraMap A (Algebra.adjoinSingletonGenerator A x) f).symm
    rw [← he]
    exact Ideal.mem_map_of_mem (algebraMap S T) hfm
  have hgq : aeval (Algebra.adjoinSingletonGenerator A x) g ∈ q := by
    change aeval (Algebra.adjoinSingletonGenerator A x)
      (f.map (algebraMap R A) * C (IsLocalization.Away.invSelf c)) ∈ q
    rw [_root_.map_mul]
    exact q.mul_mem_right _ hfq
  exact finite_atPrime_of_isLocalization S T K M m q hmq
    (finite_atMaximal_adjoin_singleton_of_monic A K hA hdimA x q g hg hgq)

/-- Finite literal normalization of a rational adjunction over a normal
Nagata domain of dimension at most two, in the original supplied field. -/
theorem finite_adjoin_singleton_of_isNagataRing_dimLE_two
    (hR : IsNagataRing.{u, 0} R) (hdim : ringKrullDim R ≤ 2) (x : K) :
    Module.Finite (Algebra.adjoin R ({x} : Set K))
      (integralClosure (Algebra.adjoin R ({x} : Set K)) K) := by
  let : IsNoetherianRing R := hR.isNoetherianRing
  let S := Algebra.adjoin R ({x} : Set K)
  let : Algebra.FiniteType R S := Algebra.FiniteType.adjoin_of_finite (Set.finite_singleton x)
  let : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing R S
  let : IsFractionRing S K := Algebra.isFractionRing_adjoin_singleton R x
  obtain ⟨b, a, ha, hba⟩ := IsFractionRing.div_surjective R x
  have ha0 : a ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp ha
  have haK : algebraMap R K a ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ha
  have hab : algebraMap R K a * x = algebraMap R K b := by
    simpa only [mul_comm] using ((div_eq_iff haK).mp hba).symm
  have haS : algebraMap R S a ≠ 0 := by
    intro h
    exact haK (congrArg (fun s : S => (s : K)) h)
  let : IsIntegrallyClosed (Localization.Away (algebraMap R S a)) :=
    Algebra.isIntegrallyClosed_away_adjoin_singleton R x a b ha0 hab
  exact finite_of_normal_away_of_finite_atMaximal S K (algebraMap R S a) haS
    (fun m _ => finite_atMaximal_adjoin_singleton_of_dimLE_two R K hR hdim x m)

end integralClosure
