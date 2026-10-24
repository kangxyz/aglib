/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.CompleteParameterMap
public import Aglib.RingTheory.LocalRing.CoefficientSection
public import Aglib.RingTheory.LocalRing.CohenMap
public import Aglib.RingTheory.LocalRing.ParameterIdeal
public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.RingTheory.DedekindDomain.PID
public import Mathlib.RingTheory.Polynomial.Ideal
public import Mathlib.RingTheory.RegularLocalRing.Polynomial

/-!
# An actual finite complete regular subring in dimension two

The source is the literal maximal-adic completion of a localized
polynomial ring at the kernel of its original residue point. Equal
characteristic uses the actual residue section and an iterated polynomial
ring. Mixed characteristic uses the constructed Cohen map and its
original prime uniformizer. All residue and completion map equations
are retained.
-/

@[expose] public noncomputable section

open IsLocalRing Polynomial

namespace IsLocalRing

universe u

private structure ParameterSource (A : Type u) [CommRing A] [IsLocalRing A] where
  ring : CommRingCat.{u}
  regular : IsRegularLocalRing ring
  dimension : ringKrullDim ring = 2
  map : ring →+* A
  radical :
    let _ : IsRegularLocalRing ring := regular
    ((maximalIdeal ring).map map).radical = maximalIdeal A
  residue_surjective : Function.Surjective ((residue A).comp map)

private theorem residue_comp_eval₂
    {D A : Type*} [CommRing D] [CommRing A] [IsLocalRing A]
    (f : D →+* A) (x : A) (hx : x ∈ maximalIdeal A) :
    (residue A).comp (Polynomial.eval₂RingHom f x) =
      ((residue A).comp f).comp Polynomial.constantCoeff := by
  apply Polynomial.ringHom_ext
  · intro d
    simp only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
      Polynomial.constantCoeff_apply, Polynomial.coeff_C_zero]
  · simpa only [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      Polynomial.constantCoeff_apply, Polynomial.coeff_X_zero, map_zero] using
      (residue_eq_zero_iff x).mpr hx

private theorem ker_comp_constantCoeff
    {D K : Type*} [CommRing D] [CommRing K] (g : D →+* K) :
    RingHom.ker (g.comp Polynomial.constantCoeff) =
      (RingHom.ker g).map Polynomial.C ⊔ Ideal.span {(Polynomial.X : Polynomial D)} := by
  have hs : Function.Surjective (Polynomial.constantCoeff : Polynomial D →+* D) :=
    fun d ↦ ⟨Polynomial.C d, Polynomial.coeff_C_zero⟩
  have hcomp : (Polynomial.constantCoeff : Polynomial D →+* D).comp Polynomial.C =
      RingHom.id D := by
    ext d
    exact Polynomial.coeff_C_zero
  have hmap : ((RingHom.ker g).map Polynomial.C).map Polynomial.constantCoeff =
      RingHom.ker g := by rw [Ideal.map_map, hcomp, Ideal.map_id]
  calc
    RingHom.ker (g.comp Polynomial.constantCoeff) =
        (RingHom.ker g).comap Polynomial.constantCoeff := by rw [RingHom.comap_ker]
    _ = (((RingHom.ker g).map Polynomial.C).map Polynomial.constantCoeff).comap
        Polynomial.constantCoeff := by rw [hmap]
    _ = (RingHom.ker g).map Polynomial.C ⊔ RingHom.ker Polynomial.constantCoeff :=
      Ideal.comap_map_of_surjective' Polynomial.constantCoeff hs _
    _ = _ := by rw [Polynomial.ker_constantCoeff]

private def polynomialParameterSource
    {D A : Type u} [CommRing D] [IsDomain D] [IsPrincipalIdealRing D]
    [CommRing A] [IsLocalRing A]
    (f : D →+* A) (t : D) (ht : Irreducible t)
    (hres : Function.Surjective ((residue A).comp f))
    (hker : RingHom.ker ((residue A).comp f) = Ideal.span {t})
    (x : A) (hx : x ∈ maximalIdeal A)
    (hparam : (Ideal.span {f t} ⊔ Ideal.span {x}).radical = maximalIdeal A) :
    ParameterSource A := by
  let g : D →+* ResidueField A := (residue A).comp f
  let e : Polynomial D →+* A := Polynomial.eval₂RingHom f x
  let z : Polynomial D →+* ResidueField A := g.comp Polynomial.constantCoeff
  let q := RingHom.ker z
  have hz : Function.Surjective z := by
    intro a
    obtain ⟨d, hd⟩ := hres a
    refine ⟨Polynomial.C d, ?_⟩
    change g (Polynomial.constantCoeff (Polynomial.C d)) = a
    rw [Polynomial.constantCoeff_apply, Polynomial.coeff_C_zero]
    exact hd
  let : q.IsMaximal := RingHom.ker_isMaximal_of_surjective z hz
  let B := Localization.AtPrime q
  let : IsRegularLocalRing B := inferInstance
  have hpoint : (residue A).comp e = z := residue_comp_eval₂ f x hx
  have hunit (s : q.primeCompl) : IsUnit (e s) := by
    apply (residue_ne_zero_iff_isUnit _).mp
    intro hs
    apply s.property
    change z s = 0
    rw [← hpoint]
    exact hs
  let fB : B →+* A := IsLocalization.lift (M := q.primeCompl) (S := B) (g := e) hunit
  have hlift (F : Polynomial D) : fB (algebraMap (Polynomial D) B F) = e F :=
    IsLocalization.lift_eq hunit F
  have hcomp : fB.comp (algebraMap (Polynomial D) B) = e :=
    RingHom.ext fun F ↦ hlift F
  have hq : q = Ideal.span {Polynomial.C t} ⊔ Ideal.span {Polynomial.X} := by
    change RingHom.ker (g.comp Polynomial.constantCoeff) = _
    rw [ker_comp_constantCoeff, hker, Ideal.map_span, Set.image_singleton]
  have hm : (maximalIdeal B).map fB = Ideal.span {f t} ⊔ Ideal.span {x} := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, hcomp, hq]
    simp only [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
    change Ideal.span {Polynomial.eval₂ f x (Polynomial.C t)} ⊔
      Ideal.span {Polynomial.eval₂ f x Polynomial.X} = _
    rw [Polynomial.eval₂_C, Polynomial.eval₂_X]
  let P := RingHom.ker g
  let : P.IsMaximal := RingHom.ker_isMaximal_of_surjective g hres
  have hqP : q.under D = P := by
    ext d
    change g (Polynomial.constantCoeff (Polynomial.C d)) = 0 ↔ g d = 0
    rw [Polynomial.constantCoeff_apply, Polynomial.coeff_C_zero]
  let : q.LiesOver P := ⟨hqP.symm⟩
  have hnot : ¬IsField D := by
    intro h
    let : Field D := h.toField
    exact ht.not_isUnit (isUnit_iff_ne_zero.mpr ht.ne_zero)
  have hPheight : P.height = 1 := IsPrincipalIdealRing.height_eq_one_of_isMaximal P hnot
  have hdim : ringKrullDim B = 2 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q B,
      Polynomial.height_eq_height_add_one P q, hPheight]
    norm_num
  have hresB : Function.Surjective ((residue A).comp fB) := by
    intro a
    obtain ⟨d, hd⟩ := hres a
    refine ⟨algebraMap (Polynomial D) B (Polynomial.C d), ?_⟩
    change residue A (fB (algebraMap (Polynomial D) B (Polynomial.C d))) = a
    rw [hlift]
    change residue A (Polynomial.eval₂ f x (Polynomial.C d)) = a
    rw [Polynomial.eval₂_C]
    exact hd
  exact {
    ring := CommRingCat.of B
    regular := (inferInstance : IsRegularLocalRing B)
    dimension := hdim
    map := fB
    radical := by
      change ((maximalIdeal B).map fB).radical = maximalIdeal A
      rw [hm]
      exact hparam
    residue_surjective := hresB }

private theorem parameterSource_of_section
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    (hd : ringKrullDim A = 2) (s : ResidueField A →+* A)
    (hs : (residue A).comp s = RingHom.id (ResidueField A)) :
    Nonempty (ParameterSource A) := by
  let : Ring.KrullDimLE 2 A := Ring.krullDimLE_iff.mpr hd.le
  have hm : maximalIdeal A ≠ ⊥ := by
    intro h
    have hz := ringKrullDim_eq_zero_of_isField (isField_iff_maximalIdeal_eq.mpr h)
    rw [hd] at hz
    norm_num at hz
  obtain ⟨a, ha, ha0⟩ := (maximalIdeal A).ne_bot_iff.mp hm
  obtain ⟨x, hx, hparam⟩ := exists_parameter_pair_containing A a ha0 ha
  let f : Polynomial (ResidueField A) →+* A := Polynomial.eval₂RingHom s a
  have he : (residue A).comp f = Polynomial.constantCoeff := by
    rw [show f = Polynomial.eval₂RingHom s a from rfl, residue_comp_eval₂ s a ha,
      hs, RingHom.id_comp]
  have hres : Function.Surjective ((residue A).comp f) := by
    rw [he]
    exact fun c ↦ ⟨Polynomial.C c, Polynomial.coeff_C_zero⟩
  have hker : RingHom.ker ((residue A).comp f) = Ideal.span {Polynomial.X} := by
    rw [he, Polynomial.ker_constantCoeff]
  have hparam' : (Ideal.span {f Polynomial.X} ⊔ Ideal.span {x}).radical = maximalIdeal A := by
    change (Ideal.span {Polynomial.eval₂ s a Polynomial.X} ⊔ Ideal.span {x}).radical = _
    rw [Polynomial.eval₂_X]
    exact hparam
  exact ⟨polynomialParameterSource f Polynomial.X Polynomial.irreducible_X hres hker x hx hparam'⟩

private theorem parameterSource_of_mixedCharacteristic
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [CharZero A] [IsAdicComplete (maximalIdeal A) A]
    (hd : ringKrullDim A = 2) (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p] :
    Nonempty (ParameterSource A) := by
  let : Ring.KrullDimLE 2 A := Ring.krullDimLE_iff.mpr hd.le
  obtain ⟨C, hD, hV, _, _, hp, f, _, _, hres⟩ :=
    IsDiscreteValuationRing.exists_complete_cohenMap A p
  let : IsDomain C := hD
  let : IsDiscreteValuationRing C := hV
  have hker : RingHom.ker ((residue A).comp f) = Ideal.span {(p : C)} :=
    (IsLocalRing.ker_eq_maximalIdeal ((residue A).comp f) hres).trans hp.maximalIdeal_eq
  have hpA : (p : A) ∈ maximalIdeal A := by
    apply (residue_eq_zero_iff _).mp
    rw [map_natCast]
    exact CharP.cast_eq_zero (ResidueField A) p
  have hpA0 : (p : A) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  obtain ⟨x, hx, hparam⟩ := exists_parameter_pair_containing A (p : A) hpA0 hpA
  have hparam' : (Ideal.span {f (p : C)} ⊔ Ideal.span {x}).radical = maximalIdeal A := by
    rw [map_natCast]
    exact hparam
  exact ⟨polynomialParameterSource f (p : C) hp hres hker x hx hparam'⟩

private theorem nonempty_parameterSource
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] (hd : ringKrullDim A = 2) :
    Nonempty (ParameterSource A) := by
  rcases CharP.exists' A with hzero | ⟨p, hp, hchar⟩
  · let : CharZero A := hzero
    rcases CharP.exists' (ResidueField A) with hkzero | ⟨p, hp, hkchar⟩
    · let : CharZero (ResidueField A) := hkzero
      obtain ⟨s, hs⟩ := exists_coefficientSection_of_residue_charZero A
      exact parameterSource_of_section A hd s hs
    · let : Fact p.Prime := hp
      let : CharP (ResidueField A) p := hkchar
      exact parameterSource_of_mixedCharacteristic A hd p
  · let : Fact p.Prime := hp
    let : CharP A p := hchar
    obtain ⟨s, hs⟩ := exists_coefficientSection_of_charP A p
    exact parameterSource_of_section A hd s hs

/-- Every complete Noetherian local domain of dimension two admits an
actual finite injective local map from a complete regular local domain
of dimension two, including arbitrary equal and mixed characteristics. -/
theorem exists_finite_complete_regular_subring
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] (hd : ringKrullDim A = 2) :
    ∃ (R : CommRingCat.{u}) (hR : IsRegularLocalRing R),
      let _ : IsRegularLocalRing R := hR
      IsDomain R ∧ IsAdicComplete (maximalIdeal R) R ∧ ringKrullDim R = 2 ∧
        ∃ f : R →+* A, Function.Injective f ∧ IsLocalHom f ∧
          (let _ : Algebra R A := f.toAlgebra; Module.Finite R A) := by
  obtain ⟨S⟩ := nonempty_parameterSource A hd
  let B := S.ring
  let : IsRegularLocalRing B := S.regular
  let R := AdicCompletion (maximalIdeal B) B
  let : IsNoetherianRing R := AdicCompletion.isNoetherianRing B (maximalIdeal B)
  let : IsRegularLocalRing R :=
    (AdicCompletion.isRegularLocalRing_iff_maximalCompletion B).mp inferInstance
  have hdomain : IsDomain R := IsRegularLocalRing.isDomain_of_regularLocal R
  have hcomplete : IsAdicComplete (maximalIdeal R) R := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact AdicCompletion.isAdicComplete_self (maximalIdeal B)
      (maximalIdeal B).fg_of_isNoetherianRing
  have hdim : ringKrullDim R = 2 :=
    (AdicCompletion.ringKrullDim_maximalIdeal_eq B).trans S.dimension
  let f : R →+* A := AdicCompletion.localParameterMap S.map S.radical
  have hinj : Function.Injective f :=
    AdicCompletion.injective_localParameterMap S.map S.radical S.residue_surjective 2 S.dimension hd
  have hlocal : IsLocalHom f := AdicCompletion.localParameterMap_isLocalHom S.map S.radical
  refine ⟨CommRingCat.of R, (inferInstance : IsRegularLocalRing R),
    hdomain, hcomplete, hdim, f, hinj, hlocal, ?_⟩
  exact AdicCompletion.finite_localParameterMap S.map S.radical S.residue_surjective

end IsLocalRing
