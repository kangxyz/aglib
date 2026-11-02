/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Excellent.FiniteBranches
public import Aglib.RingTheory.Excellent.NormalCompletion
public import Aglib.RingTheory.LocalizedPrimeBranches
public import Aglib.RingTheory.AdicCompletion.RingEquiv
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# Normal completion at original prime points of finite G-ring algebras

Localize the original finite algebra over the contraction of the selected
prime. The existing double-localization equivalence identifies its selected
branch with the original local ring. The original regular completion map of
the G-ring base transfers to this branch. Both normal-domain conclusions are
transported back by the literal completion ring equivalence.
-/

@[expose] public noncomputable section

open IsLocalRing

universe u

namespace AdicCompletion

/-- A normal-domain local ring of dimension two at an original prime of a
finite algebra over a G-ring has normal-domain actual completion. No global
normality of the finite algebra or finiteness of its local branch is assumed. -/
theorem normalDomain_of_finite_of_isGRing
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (hG : IsGRing R) (q : Ideal S) [q.IsPrime]
    [IsDomain (Localization.AtPrime q)] [IsIntegrallyClosed (Localization.AtPrime q)]
    (hdim : ringKrullDim (Localization.AtPrime q) = 2) :
    IsDomain (AdicCompletion (maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)) ∧
    IsIntegrallyClosed (AdicCompletion (maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime q)) := by
  let : IsNoetherianRing R := hG.1
  let : IsNoetherianRing S := IsNoetherianRing.of_finite R S
  let p := q.under R
  let A := Localization.AtPrime p
  let B := Localization (p.primeCompl.map (algebraMap R S))
  let : IsNoetherianRing A := IsLocalization.isNoetherianRing p.primeCompl A inferInstance
  let : IsNoetherianRing B := IsLocalization.isNoetherianRing
    (p.primeCompl.map (algebraMap R S)) B inferInstance
  let : IsLocalization (Algebra.algebraMapSubmonoid S p.primeCompl) B := by
    change IsLocalization (p.primeCompl.map (algebraMap R S)) B
    infer_instance
  let : Algebra A B := _root_.localizationAlgebra (Rₘ := A) (Sₘ := B) p.primeCompl S
  let : IsScalarTower R A B :=
    _root_.isScalarTower_localizationAlgebra (Rₘ := A) (Sₘ := B) p.primeCompl S
  let : Module.Finite A B := Module.Finite.of_isLocalization R S p.primeCompl
  let Q := q.map (algebraMap S B)
  let : Q.IsPrime := Localization.isPrime_map_basePrimeCompl p q rfl
  have hQR : Q.comap (algebraMap R B) = p := by
    rw [IsScalarTower.algebraMap_eq R S B, ← Ideal.comap_comap]
    change (Q.under S).under R = p
    rw [Localization.under_map_basePrimeCompl p q rfl]
  have hQA : Q.comap (algebraMap A B) = maximalIdeal A := by
    apply (Localization.AtPrime.eq_maximalIdeal_iff_under_eq (I := p)).mp
    change (Q.comap (algebraMap A B)).comap (algebraMap R A) = p
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq R A B]
    exact hQR
  let T := Localization.AtPrime Q
  let L := Localization.AtPrime q
  let e : T ≃ₐ[S] L := Localization.atPrimeBasePrimeComplEquiv p q rfl
  let : IsDomain T := Function.Injective.isDomain e.toRingHom e.injective
  let : IsIntegrallyClosed T := IsIntegrallyClosed.of_equiv e.toRingEquiv.symm
  have hTdim : ringKrullDim T = 2 := e.toRingEquiv.ringKrullDim.trans hdim
  have hregular : Algebra.IsRegularMap T (AdicCompletion (maximalIdeal T) T) :=
    FiniteSemilocal.regularMap_localCompletion A B (hG.2 p) Q hQA
  obtain ⟨hdom, hnormal⟩ := normalDomain_of_regularMap_of_dim_eq_two T hTdim hregular
  let : IsDomain (AdicCompletion (maximalIdeal T) T) := hdom
  let : IsIntegrallyClosed (AdicCompletion (maximalIdeal T) T) := hnormal
  have hm : (maximalIdeal T).map e.toRingEquiv.toRingHom = maximalIdeal L :=
    map_ringEquiv_maximalIdeal e.toRingEquiv
  let ec : AdicCompletion (maximalIdeal T) T ≃+* AdicCompletion (maximalIdeal L) L :=
    hm ▸ AdicCompletion.congrRingEquiv e.toRingEquiv (maximalIdeal T)
  exact ⟨Function.Injective.isDomain ec.symm.toRingHom ec.symm.injective,
    IsIntegrallyClosed.of_equiv ec⟩

end AdicCompletion
