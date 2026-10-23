/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Ideal.AssociatedPrime.FlatBaseChange
public import Aglib.RingTheory.Ideal.AssociatedPrime.Reduced
public import Aglib.RingTheory.RegularLocalRing.QuotientLift
public import Aglib.RingTheory.RegularLocalRing.Domain
public import Aglib.RingTheory.AdicCompletion.FiniteAlgebra
public import Aglib.RingTheory.AdicCompletion.NoetherianRing
public import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.AdicCompletion.Noetherian
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalProperties.Reduced

/-!
# Actual completion specialization of the associated-prime criterion

The ambient localizations at the associated primes are explicitly assumed
to be DVRs. The completed prime quotients use their actual canonical maps.
Deriving the DVR input from classical ambient regularity or from each
normalization and rational-adjunction consumer remains separate.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open IsLocalRing

universe u

/-- A reduced prime-quotient fiber at an associated point of a flat
algebra over an actual localized DVR has regular ambient local ring. -/
theorem IsRegularLocalRing.atPrime_of_flat_of_dvr_of_reduced_quotient
    (R S : Type u) [CommRing R] [CommRing S] [IsNoetherianRing S]
    [Algebra R S] [Module.Flat R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (hpq : p = q.comap (algebraMap R S))
    [IsDomain (Localization.AtPrime p)] [IsDiscreteValuationRing (Localization.AtPrime p)]
    [IsReduced (S ⧸ p.map (algebraMap R S))]
    (hq : IsAssociatedPrime q (S ⧸ p.map (algebraMap R S))) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  let A := Localization.AtPrime p
  let C := Localization.AtPrime q
  let I : Ideal S := p.map (algebraMap R S)
  let J : Ideal C := I.map (algebraMap S C)
  let e : A →+* C := Localization.localRingHom p q (algebraMap R S) hpq
  let : Algebra A C := e.toAlgebra
  let : IsScalarTower R A C := IsScalarTower.of_algebraMap_eq fun r => by
    change algebraMap R C r = e (algebraMap R A r)
    rw [show e (algebraMap R A r) = algebraMap S C (algebraMap R S r) from
      Localization.localRingHom_to_map p q (algebraMap R S) hpq r]
    exact IsScalarTower.algebraMap_apply R S C r
  let : Module.Flat R C := inferInstance
  let : Module.Flat A C :=
    (Module.flat_iff_of_isLocalization A p.primeCompl C).mpr inferInstance
  let : IsNoetherianRing C :=
    IsLocalization.isNoetherianRing q.primeCompl C inferInstance
  let : Algebra (S ⧸ I) (C ⧸ J) := inferInstance
  let : IsScalarTower S (S ⧸ I) (C ⧸ J) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let f : (S ⧸ I) →ₗ[S] C ⧸ J :=
    (IsScalarTower.toAlgHom S (S ⧸ I) (C ⧸ J)).toLinearMap
  let : IsLocalizedModule q.primeCompl f := inferInstance
  let : IsReduced (C ⧸ J) :=
    isReduced_localizationPreserves
      (Algebra.algebraMapSubmonoid (S ⧸ I) q.primeCompl) (C ⧸ J) inferInstance
  have hqLocal : IsAssociatedPrime (maximalIdeal C) (C ⧸ J) := by
    apply (open Module.associatedPrimes in
      mem_associatedPrimes_of_comap_mem_associatedPrimes_of_isLocalizedModule)
      q.primeCompl f
    change IsAssociatedPrime ((maximalIdeal (Localization.AtPrime q)).under S) (S ⧸ I)
    rwa [Localization.AtPrime.under_maximalIdeal]
  have hJmax : J = maximalIdeal C :=
    J.eq_maximalIdeal_of_isReduced_quotient_of_isAssociatedPrime hqLocal
  have hpmap : p.map (algebraMap R A) = maximalIdeal A :=
    Localization.AtPrime.map_eq_maximalIdeal (I := p)
  have hJ : J = (maximalIdeal A).map (algebraMap A C) := by
    rw [← hpmap, Ideal.map_map, ← IsScalarTower.algebraMap_eq R A C]
    change (p.map (algebraMap R S)).map (algebraMap S C) = p.map (algebraMap R C)
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R S C]
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hmax : maximalIdeal C = Ideal.span {algebraMap A C π} := by
    rw [← hJmax, hJ, hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  let : (Ideal.span {algebraMap A C π}).IsMaximal := by
    rw [← hmax]
    infer_instance
  let : Field (C ⧸ Ideal.span {algebraMap A C π}) := Ideal.Quotient.field _
  have hregA : IsSMulRegular A π :=
    IsSMulRegular.of_right_eq_zero_of_smul fun z hz =>
      (mul_eq_zero.mp (show π * z = 0 from hz)).resolve_left hπ.ne_zero
  have hregC : IsSMulRegular C (algebraMap A C π) := hregA.of_flat
  exact IsRegularLocalRing.of_quotient_span_singleton C (algebraMap A C π) hregC

/-- The algebraic associated-DVR criterion before specializing the flat
algebra to a completion. The DVR hypotheses concern ambient local rings. -/
theorem IsReduced.of_flat_of_associated_dvr_quotients
    (R S : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [CommRing S] [IsNoetherianRing S] [Algebra R S] [Module.Flat R S]
    (x : R) (hx : x ≠ 0) [IsHausdorff (Ideal.span {algebraMap R S x}) S]
    (hdvr : ∀ (p : Ideal R) [p.IsPrime], IsAssociatedPrime p (R ⧸ Ideal.span {x}) →
      IsDiscreteValuationRing (Localization.AtPrime p))
    (hred : ∀ (p : Ideal R) [p.IsPrime], IsAssociatedPrime p (R ⧸ Ideal.span {x}) →
      IsReduced (S ⧸ p.map (algebraMap R S))) : IsReduced S := by
  have hregR : IsSMulRegular R x := fun _ _ h => mul_left_cancel₀ hx h
  have hregS : IsSMulRegular S (algebraMap R S x) := hregR.of_flat
  have hxS : algebraMap R S x ∈ nonZeroDivisors S :=
    mem_nonZeroDivisors_iff_left.mpr fun z hz => hregS.right_eq_zero_of_smul hz
  apply IsReduced.of_isHausdorff_of_associated_localizations (algebraMap R S x) hxS
  intro q hq hass
  let I : Ideal R := Ideal.span {x}
  have hI : I.map (algebraMap R S) = Ideal.span {algebraMap R S x} := by
    simp only [I, Ideal.map_span, Set.image_singleton]
  let e : (S ⧸ Ideal.span {algebraMap R S x}) ≃ₗ[S] S ⊗[R] (R ⧸ I) :=
    (Ideal.quotientEquivAlgOfEq S hI.symm).toLinearEquiv.trans
      (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S I).toLinearEquiv
  have hassTensor : IsAssociatedPrime q (S ⊗[R] (R ⧸ I)) :=
    e.isAssociatedPrime_iff.mp hass
  obtain ⟨p, hp, hqp, hassp⟩ := hassTensor.exists_quotient_of_flat_tensorProduct
  let : p.IsPrime := hp.isPrime
  let : IsDiscreteValuationRing (Localization.AtPrime p) := hdvr p hp
  let : IsReduced (S ⧸ p.map (algebraMap R S)) := hred p hp
  let : IsRegularLocalRing (Localization.AtPrime q) :=
    IsRegularLocalRing.atPrime_of_flat_of_dvr_of_reduced_quotient R S p q hqp.symm hassp
  let : IsDomain (Localization.AtPrime q) :=
    IsRegularLocalRing.isDomain_of_regularLocal (Localization.AtPrime q)
  infer_instance

namespace AdicCompletion

local instance primeQuotient_isLocalRing
    {R : Type u} [CommRing R] [IsLocalRing R] (p : Ideal R) [p.IsPrime] :
    IsLocalRing (R ⧸ p) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective

/-- The original quotient of the completed local ring is the actual
maximal-ideal completion of the original prime quotient. -/
def quotientEquivPrimeCompletion
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (p : Ideal R) [p.IsPrime] :
    ((AdicCompletion (maximalIdeal R) R) ⧸
      p.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) ≃+*
      AdicCompletion (maximalIdeal (R ⧸ p)) (R ⧸ p) := by
  let B := AdicCompletion (maximalIdeal R) R
  let e := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B p).toRingEquiv.trans
    (tensorEquivExtendedCompletion (S := R ⧸ p) (maximalIdeal R)).toRingEquiv
  have hmax : (maximalIdeal R).map (algebraMap R (R ⧸ p)) = maximalIdeal (R ⧸ p) := by
    change (maximalIdeal R).map (Ideal.Quotient.mk p) = maximalIdeal (R ⧸ p)
    exact IsLocalRing.map_maximalIdeal_of_surjective _ Ideal.Quotient.mk_surjective
  rw [hmax] at e
  exact e

private theorem isReduced_of_ringEquiv
    {A B : Type u} [CommRing A] [CommRing B] (e : A ≃+* B) (hB : IsReduced B) :
    IsReduced A := by
  let : IsReduced B := hB
  exact isReduced_of_injective e e.injective

private theorem isReduced_primeQuotient_of_primeCompletion
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (p : Ideal R) [p.IsPrime]
    (h : IsReduced (AdicCompletion (maximalIdeal (R ⧸ p)) (R ⧸ p))) :
    IsReduced ((AdicCompletion (maximalIdeal R) R) ⧸
      p.map (algebraMap R (AdicCompletion (maximalIdeal R) R))) :=
  isReduced_of_ringEquiv (quotientEquivPrimeCompletion R p) h

/-- The actual maximal-ideal completion is reduced under the explicit
associated-DVR and reduced prime-quotient-completion premises. -/
theorem isReduced_of_associated_dvr_quotients
    (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    (x : R) (hx : x ∈ maximalIdeal R) (hx0 : x ≠ 0)
    (hdvr : ∀ (p : Ideal R) [p.IsPrime], IsAssociatedPrime p (R ⧸ Ideal.span {x}) →
      IsDiscreteValuationRing (Localization.AtPrime p))
    (hred : ∀ (p : Ideal R) [p.IsPrime], IsAssociatedPrime p (R ⧸ Ideal.span {x}) →
      IsReduced (AdicCompletion (maximalIdeal (R ⧸ p)) (R ⧸ p))) :
    IsReduced (AdicCompletion (maximalIdeal R) R) := by
  let B := AdicCompletion (maximalIdeal R) R
  let : IsNoetherianRing B := AdicCompletion.isNoetherianRing R (maximalIdeal R)
  have hxB : algebraMap R B x ∈ maximalIdeal B := by
    change x ∈ (maximalIdeal B).comap (algebraMap R B)
    rw [IsLocalRing.maximalIdeal_comap]
    exact hx
  have hproper : Ideal.span {algebraMap R B x} ≠ ⊤ :=
    ne_top_of_le_ne_top (maximalIdeal.isMaximal B).ne_top
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hxB))
  let : IsHausdorff (Ideal.span {algebraMap R B x}) B :=
    IsHausdorff.of_isLocalRing _ _ hproper
  apply IsReduced.of_flat_of_associated_dvr_quotients R B x hx0 hdvr
  intro p hp hass
  exact isReduced_primeQuotient_of_primeCompletion R p (hred p hass)

end AdicCompletion
