/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Normalization.GenericFiniteEtale.EtaleBaseChange
public import Aglib.AlgebraicGeometry.Spec.ParameterComplementBaseChange
public import Aglib.AlgebraicGeometry.Properties.Regular.Basic
public import Aglib.RingTheory.RegularLocalRing.Normal
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Unramified.LocalStructure

/-! # The genuine regular-stage parameter normalization comparison

This thin specialization uses the original parameter-complement square and
native smooth normalization comparison. All three original triangles are
retained, including the original covering-source inclusion.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Algebra.Kummer

namespace AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery

universe u

variable (R B : Type u) [CommRing R] [IsDomain R] [IsRegularRing R]
  [CommRing B] [IsDomain B] [IsRegularRing B] [Algebra R B] [Algebra.Etale R B]
  (f : R) (hf : f ≠ 0)

omit [IsRegularRing R] [IsRegularRing B] in
include hf in
/-- A genuine etale domain stage does not kill the original nonzero parameter. -/
theorem parameter_etale_algebraMap_ne_zero : algebraMap R B f ≠ 0 := by
  let : Module.Flat R B := inferInstance
  simpa only [map_zero] using (FaithfulSMul.algebraMap_injective R B).ne hf

/-- The actual original normalization at a genuine regular domain stage.
The comparison, structural equation, generic source and original open-cover
map are all constructed, not supplied as premises. -/
theorem exists_parameterNormalizationBaseChangeIso
    (Y : FiniteEtale (Spec (.of (Localization.Away f)))) :
    letI : IsDomain (Localization.Away f) := Localization.Away.isDomain hf
    letI : IsDomain (Localization.Away (algebraMap R B f)) :=
      Localization.Away.isDomain (parameter_etale_algebraMap_ne_zero R B f hf)
    let j := Spec.algebraMap R (Localization.Away f)
    let jB := Spec.algebraMap B (Localization.Away (algebraMap R B f))
    let b := Spec.algebraMap R B
    let g := Spec.map (CommRingCat.ofHom (parameterComplementBaseChangeHom B f))
    letI : IsDominant g := Scheme.Kummer.parameterComplementBaseChange_dominant R B f hf
    let q₀ := genericMap j Y.obj.hom
    let qB := genericMap jB ((baseChange g).obj Y).obj.hom
    letI : ∀ x : Spec (.of R), IsIntegrallyClosed ((Spec (.of R)).presheaf.stalk x) :=
      fun x => @IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _ _
        (regularStalks_spec R x)
    letI : ∀ x : Spec (.of B), IsIntegrallyClosed ((Spec (.of B)).presheaf.stalk x) :=
      fun x => @IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _ _
        (regularStalks_spec B x)
    ∃ e : qB.normalization ≅ pullback q₀.fromNormalization b,
      e.hom ≫ pullback.snd _ _ = qB.fromNormalization ∧
      qB.toNormalization ≫ e.hom ≫ pullback.fst _ _ =
        genericPullbackMap g Y.obj.hom ≫ q₀.toNormalization ∧
      inclusion jB ((baseChange g).obj Y).obj.hom ≫ e.hom ≫ pullback.fst _ _ =
        pullback.fst Y.obj.hom g ≫ inclusion j Y.obj.hom := by
  let : IsDomain (Localization.Away f) := Localization.Away.isDomain hf
  let : IsDomain (Localization.Away (algebraMap R B f)) :=
    Localization.Away.isDomain (parameter_etale_algebraMap_ne_zero R B f hf)
  let j := Spec.algebraMap R (Localization.Away f)
  let jB := Spec.algebraMap B (Localization.Away (algebraMap R B f))
  let b := Spec.algebraMap R B
  let g := Spec.map (CommRingCat.ofHom (parameterComplementBaseChangeHom B f))
  let : Etale b := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr
    (RingHom.etale_algebraMap.mpr inferInstance)
  let : Etale g := Scheme.Kummer.parameterComplementBaseChange_etale R B f
  let : IsDominant g := Scheme.Kummer.parameterComplementBaseChange_dominant R B f hf
  let : ∀ x : Spec (.of R), IsIntegrallyClosed ((Spec (.of R)).presheaf.stalk x) := by
    intro x
    let : IsRegularLocalRing ((Spec (.of R)).presheaf.stalk x) := regularStalks_spec R x
    exact IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _
  let : ∀ x : Spec (.of B), IsIntegrallyClosed ((Spec (.of B)).presheaf.stalk x) := by
    intro x
    let : IsRegularLocalRing ((Spec (.of B)).presheaf.stalk x) := regularStalks_spec B x
    exact IsRegularLocalRing.isIntegrallyClosed_of_regularLocal _
  let H := Scheme.Kummer.parameterComplementBaseChange_isPullback R B f
  let : LocallyQuasiFinite b :=
    (HasRingHomProperty.Spec_iff (P := @LocallyQuasiFinite)).mpr
      (RingHom.quasiFinite_algebraMap.mpr inferInstance)
  let : LocallyQuasiFinite g := MorphismProperty.of_isPullback H.flip inferInstance
  exact ⟨etaleBaseChangeIso j jB b g H Y,
    etaleBaseChangeIso_hom_snd j jB b g H Y,
    etaleBaseChangeIso_hom_generic j jB b g H Y,
    inclusion_etaleBaseChangeIso_hom_fst j jB b g H Y⟩

end AlgebraicGeometry.Scheme.FiniteEtale.GenericNormalization.OpenRecovery
