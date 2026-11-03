/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdicCompletion.CompleteParameterMap
public import Aglib.RingTheory.LocalRing.CoefficientSection
public import Aglib.RingTheory.LocalRing.CohenMap
public import Aglib.RingTheory.LocalRing.ParameterFamily
public import Aglib.RingTheory.LocalRing.PolynomialParameterSource
public import Mathlib.RingTheory.DedekindDomain.PID
public import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Actual finite complete regular subrings in arbitrary finite dimension

The coefficient section or original Cohen DVR map supplies the coefficient
ring. The single polynomial residue-point localization construction supplies
the regular parameter source. Completing its original map gives finiteness
and injectivity in the original target, without a dimension-two restriction.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace IsLocalRing

universe u

private theorem polynomialSource_of_section
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (d : ℕ) (hd : ringKrullDim A = (d : ℕ)) (s : ResidueField A →+* A)
    (hs : (residue A).comp s = RingHom.id (ResidueField A)) :
    Nonempty (PolynomialParameterSource A d) := by
  classical
  obtain ⟨t, ht, hrad⟩ := exists_parameter_finset A d hd
  let enum : Fin d ≃ t := (Fintype.equivFinOfCardEq (by simpa using ht)).symm
  let x : Fin d → A := fun i ↦ (enum i).val
  have hrange : Set.range x = (t : Set A) := by
    ext a
    constructor
    · rintro ⟨i, rfl⟩
      exact (enum i).property
    · intro ha
      exact ⟨enum.symm ⟨a, ha⟩, congrArg Subtype.val (enum.apply_symm_apply ⟨a, ha⟩)⟩
  have hx (i : Fin d) : x i ∈ maximalIdeal A := by
    rw [← hrad]
    exact Ideal.le_radical (Ideal.subset_span (enum i).property)
  have hker : RingHom.ker ((residue A).comp s) = ⊥ := by
    rw [hs]
    exact (RingHom.injective_iff_ker_eq_bot _).mp Function.injective_id
  have hres : Function.Surjective ((residue A).comp s) := by
    rw [hs]
    exact Function.surjective_id
  have hh : (RingHom.ker ((residue A).comp s)).height = (0 : ℕ∞) := by
    rw [hker, Ideal.height_bot]
  have hp : ((RingHom.ker ((residue A).comp s)).map s ⊔
      Ideal.span (Set.range x)).radical = maximalIdeal A := by
    rw [hker, Ideal.map_bot, bot_sup_eq, hrange]
    exact hrad
  simpa only [Nat.zero_add] using
    (show Nonempty (PolynomialParameterSource A (0 + d)) from
      ⟨PolynomialParameterSource.of_parameters s hres 0 d hh x hx hp⟩)

private theorem polynomialSource_of_mixedCharacteristic
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [CharZero A] [IsAdicComplete (maximalIdeal A) A]
    (d : ℕ) (hd : ringKrullDim A = (d : ℕ))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField A) p] :
    Nonempty (PolynomialParameterSource A d) := by
  have hpA : (p : A) ∈ maximalIdeal A := by
    apply (residue_eq_zero_iff _).mp
    rw [map_natCast]
    exact CharP.cast_eq_zero (ResidueField A) p
  have hpA0 : (p : A) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  cases d with
  | zero =>
    let : Ring.KrullDimLE 0 A := Ring.krullDimLE_iff.mpr hd.le
    have hm : maximalIdeal A = ⊥ :=
      isField_iff_maximalIdeal_eq.mp (Ring.KrullDimLE.isField_of_isDomain (R := A))
    exact (hpA0 (by simpa [hm] using hpA)).elim
  | succ d =>
    obtain ⟨C, hD, hV, _, _, hp, f, _, _, hres⟩ :=
      IsDiscreteValuationRing.exists_complete_cohenMap A p
    let : IsDomain C := hD
    let : IsDiscreteValuationRing C := hV
    have hker : RingHom.ker ((residue A).comp f) = maximalIdeal C :=
      IsLocalRing.ker_eq_maximalIdeal ((residue A).comp f) hres
    have hnot : ¬ IsField C := by
      intro h
      let : Field C := h.toField
      exact hp.not_isUnit (isUnit_iff_ne_zero.mpr hp.ne_zero)
    have hh : (RingHom.ker ((residue A).comp f)).height = (1 : ℕ∞) := by
      rw [hker]
      exact IsPrincipalIdealRing.height_eq_one_of_isMaximal (maximalIdeal C) hnot
    obtain ⟨x, hx, hparam⟩ := exists_parameter_family_containing A d hd.le (p : A) hpA0 hpA
    have hp' : ((RingHom.ker ((residue A).comp f)).map f ⊔
        Ideal.span (Set.range x)).radical = maximalIdeal A := by
      rw [hker, hp.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, map_natCast]
      exact hparam
    simpa only [Nat.add_comm 1 d] using
      (show Nonempty (PolynomialParameterSource A (1 + d)) from
        ⟨PolynomialParameterSource.of_parameters f hres 1 d hh x hx hp'⟩)

private theorem nonempty_polynomialSource
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] (d : ℕ) (hd : ringKrullDim A = (d : ℕ)) :
    Nonempty (PolynomialParameterSource A d) := by
  rcases CharP.exists' A with hzero | ⟨p, hp, hchar⟩
  · let : CharZero A := hzero
    rcases CharP.exists' (ResidueField A) with hkzero | ⟨p, hp, hkchar⟩
    · let : CharZero (ResidueField A) := hkzero
      obtain ⟨s, hs⟩ := exists_coefficientSection_of_residue_charZero A
      exact polynomialSource_of_section A d hd s hs
    · let : Fact p.Prime := hp
      let : CharP (ResidueField A) p := hkchar
      exact polynomialSource_of_mixedCharacteristic A d hd p
  · let : Fact p.Prime := hp
    let : CharP A p := hchar
    obtain ⟨s, hs⟩ := exists_coefficientSection_of_charP A p
    exact polynomialSource_of_section A d hd s hs

/-- Every complete Noetherian local domain of finite dimension admits an
actual finite injective local map from a complete regular local domain
of the same dimension, in arbitrary equal or mixed characteristic. -/
theorem exists_finite_complete_regular_subring_of_dimension
    (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A]
    [IsAdicComplete (maximalIdeal A) A] (d : ℕ) (hd : ringKrullDim A = (d : ℕ)) :
    ∃ (R : CommRingCat.{u}) (hR : IsRegularLocalRing R),
      let _ : IsRegularLocalRing R := hR
      IsDomain R ∧ IsAdicComplete (maximalIdeal R) R ∧ ringKrullDim R = (d : ℕ) ∧
        ∃ f : R →+* A, Function.Injective f ∧ IsLocalHom f ∧
          (let _ : Algebra R A := f.toAlgebra; Module.Finite R A) := by
  obtain ⟨S⟩ := nonempty_polynomialSource A d hd
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
  have hdim : ringKrullDim R = (d : ℕ) :=
    (AdicCompletion.ringKrullDim_maximalIdeal_eq B).trans S.dimension
  let f : R →+* A := AdicCompletion.localParameterMap S.map S.radical
  have hinj : Function.Injective f :=
    AdicCompletion.injective_localParameterMap S.map S.radical S.residue_surjective d S.dimension hd
  have hlocal : IsLocalHom f := AdicCompletion.localParameterMap_isLocalHom S.map S.radical
  refine ⟨CommRingCat.of R, (inferInstance : IsRegularLocalRing R),
    hdomain, hcomplete, hdim, f, hinj, hlocal, ?_⟩
  exact AdicCompletion.finite_localParameterMap S.map S.radical S.residue_surjective

end IsLocalRing
