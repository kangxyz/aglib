/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Stalk.GenericSection
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Pasting
public import Aglib.AlgebraicGeometry.Stalk.GenericFiber

/-!
# The actual prime-inverted arithmetic model

This constructs the literal base change along Spec(A[1/ell]) -> Spec(A),
its original section, and prime-power invertibility in its actual stalks.
Supporting K2-018#prop:k2018-arithmetic-characters at mathematical revision
e73d98b1b5c1e5abcdebf7d058e436d792b87982. No model-H1, purity, or etaleness
comparison is assumed or concluded.
-/


/-!
Native migration from `R5Lab.Aglib.AlgebraicGeometry.BaseChange.PrimeInversion` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`12b3371e2d5235d75c4ac1d015cec1558f14d3d389f93c6de4c75b80b3128777`.
Original objects, maps, universes and explicit hypotheses are retained.
Native providers replace duplicate implementations.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.GenericSection

universe u
namespace AlgebraicGeometry.Scheme.PrimeInversion

variable (A : Type u) [CommRing A] (ell : ℕ)

/-- The localization of `A` obtained by inverting the image of `ell`. -/
abbrev Ring := Localization.Away (ell : A)

/-- The spectrum map induced by inverting `ell` in `A`. -/
def baseMap : Spec (.of (Ring A ell)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (Ring A ell)))

variable {Y : Scheme.{u}} (p : Y ⟶ Spec (.of A))

/-- The base change of `Y` along the localization map that inverts `ell`. -/
abbrev model := pullback p (baseMap A ell)
/-- The projection from the prime-inverted base change to the original scheme `Y`. -/
abbrev projection : model A ell p ⟶ Y := pullback.fst p (baseMap A ell)
/-- The structure morphism of the prime-inverted model over the localized base. -/
abbrev structural : model A ell p ⟶ Spec (.of (Ring A ell)) :=
  pullback.snd p (baseMap A ell)

@[reassoc] theorem structural_square :
    projection A ell p ≫ p = structural A ell p ≫ baseMap A ell :=
  pullback.condition

instance baseMap_isOpenImmersion : IsOpenImmersion (baseMap A ell) := by
  change IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap A (Ring A ell))))
  infer_instance

instance projection_isOpenImmersion : IsOpenImmersion (projection A ell p) := by
  change IsOpenImmersion (pullback.fst p (baseMap A ell))
  infer_instance

/-- Prime inversion preserves every actual local ring at a surviving model point. -/
def stalkEquiv (x : model A ell p) :
    Y.presheaf.stalk (projection A ell p x) ≃+* (model A ell p).presheaf.stalk x :=
  (asIso ((projection A ell p).stalkMap x)).commRingCatIsoToRingEquiv

instance model_stalk_integrallyClosed
    [∀ y : Y, IsIntegrallyClosed (Y.presheaf.stalk y)] (x : model A ell p) :
    IsIntegrallyClosed ((model A ell p).presheaf.stalk x) :=
  IsIntegrallyClosed.of_equiv (stalkEquiv A ell p x)

instance model_locallyNoetherian [IsLocallyNoetherian Y] :
    IsLocallyNoetherian (model A ell p) :=
  isLocallyNoetherian_of_isOpenImmersion (projection A ell p)

variable (sigma : Spec (.of A) ⟶ Y) (hsigma : sigma ≫ p = 𝟙 _)

/-- The section of the prime-inverted model induced by the original section `sigma`. -/
def originSection : Spec (.of (Ring A ell)) ⟶ model A ell p :=
  pullback.lift (baseMap A ell ≫ sigma) (𝟙 _)
    (by simp only [Category.assoc, hsigma, Category.comp_id, Category.id_comp])

@[simp, reassoc] theorem section_projection :
    originSection A ell p sigma hsigma ≫ projection A ell p = baseMap A ell ≫ sigma :=
  pullback.lift_fst _ _ _

@[simp, reassoc] theorem section_structural :
    originSection A ell p sigma hsigma ≫ structural A ell p = 𝟙 _ :=
  pullback.lift_snd _ _ _

include sigma hsigma in
theorem model_nonempty [Nontrivial (Ring A ell)] : Nonempty (model A ell p) := by
  obtain ⟨x⟩ : Nonempty (Spec (.of (Ring A ell))) := inferInstance
  exact ⟨originSection A ell p sigma hsigma x⟩

include sigma hsigma in
/-- The original section supplies nonemptiness, so the localized model stays integral. -/
theorem model_integral_of_section [IsIntegral Y] [IsDomain A] (hell : (ell : A) ≠ 0) :
    IsIntegral (model A ell p) := by
  let : IsDomain (Ring A ell) := Localization.Away.isDomain hell
  let := model_nonempty A ell p sigma hsigma
  exact isIntegral_of_isOpenImmersion (projection A ell p)

/-- The actual stalk map from the localized arithmetic base. -/
def baseToStalk (x : model A ell p) : Ring A ell →+* (model A ell p).presheaf.stalk x :=
  ((StructureSheaf.toStalk (Ring A ell) (structural A ell p x)) ≫
    (structural A ell p).stalkMap x).hom

theorem prime_isUnit_stalk (x : model A ell p) :
    IsUnit (ell : (model A ell p).presheaf.stalk x) := by
  have h : IsUnit (ell : Ring A ell) := by
    simpa only [map_natCast] using
      (IsLocalization.Away.algebraMap_isUnit (S := Ring A ell) (ell : A))
  simpa only [map_natCast] using h.map (baseToStalk A ell p x)

/-- Includes r=0, hence level one. No primality assumption is needed for inversion. -/
theorem primePower_isUnit_stalk (r : ℕ) (x : model A ell p) :
    IsUnit ((ell ^ r : ℕ) : (model A ell p).presheaf.stalk x) := by
  simpa only [Nat.cast_pow] using (prime_isUnit_stalk A ell p x).pow r

section Generic

variable (F : Type u) [Field F] [Algebra A F] (hell : (ell : F) ≠ 0)

/-- The original constants map extends uniquely through the actual localization. -/
def toField : Ring A ell →+* F :=
  IsLocalization.Away.lift (ell : A)
    (show IsUnit (algebraMap A F (ell : A)) by
      simpa only [map_natCast] using (isUnit_iff_ne_zero.mpr hell))

@[simp] theorem toField_constants :
    (toField A ell F hell).comp (algebraMap A (Ring A ell)) = algebraMap A F :=
  IsLocalization.Away.lift_comp _ _

/-- The spectrum map from `F` to the localized base, using invertibility of `ell` in `F`. -/
def localizedGenericMap : Spec (.of F) ⟶ Spec (.of (Ring A ell)) :=
  Spec.map (CommRingCat.ofHom (toField A ell F hell))

@[simp, reassoc] theorem localizedGenericMap_baseMap :
    localizedGenericMap A ell F hell ≫ baseMap A ell =
        Scheme.LocalRing.GenericFiber.baseMap A F := by
  rw [localizedGenericMap, baseMap, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (toField_constants A ell F hell)

/-- Prime inversion retains the same original generic fibre, with its canonical projections. -/
def genericIso : pullback (structural A ell p) (localizedGenericMap A ell F hell) ≅
    Scheme.LocalRing.GenericFiber.scheme A F p :=
  (pullbackLeftPullbackSndIso p (baseMap A ell) (localizedGenericMap A ell F hell)).trans
    (pullback.congrHom rfl (localizedGenericMap_baseMap A ell F hell))

@[simp, reassoc] theorem genericIso_projection :
    (genericIso A ell p F hell).hom ≫
        Scheme.LocalRing.GenericFiber.projection A F p =
      pullback.fst (structural A ell p) (localizedGenericMap A ell F hell) ≫
        projection A ell p := by
  simp [genericIso, Scheme.LocalRing.GenericFiber.projection,
      pullback.map, pullback.lift_fst, Category.assoc]

@[simp, reassoc] theorem genericIso_structure :
    (genericIso A ell p F hell).hom ≫ pullback.snd p
        (Scheme.LocalRing.GenericFiber.baseMap A F) =
      pullback.snd (structural A ell p) (localizedGenericMap A ell F hell) := by
  simp [genericIso, pullback.map, pullback.lift_snd, Category.assoc]

/-- The generic-fibre section induced by the section of the prime-inverted model. -/
def localizedGenericOrigin : Spec (.of F) ⟶
    pullback (structural A ell p) (localizedGenericMap A ell F hell) :=
  pullback.lift (localizedGenericMap A ell F hell ≫ originSection A ell p sigma hsigma)
    (𝟙 _)
    (by simp only [Category.assoc, section_structural, Category.comp_id, Category.id_comp])

/-- The localized generic section is the original arithmetic origin under the constructed iso. -/
theorem genericIso_origin :
    localizedGenericOrigin A ell p sigma hsigma F hell ≫ (genericIso A ell p F hell).hom =
      genericSection A F p sigma hsigma := by
  apply pullback.hom_ext
  · simp [localizedGenericOrigin, Category.assoc, pullback.lift_fst_assoc,
      localizedGenericMap_baseMap_assoc]
  · simp [localizedGenericOrigin, Category.assoc, pullback.lift_snd]

end Generic

section FunctionField

variable [IsIntegral Y] [IsIntegral (model A ell p)]

instance projection_isDominant : IsDominant (projection A ell p) :=
  ⟨(projection A ell p).isOpenEmbedding.isOpenMap.denseRange_of_isPreirreducibleSpace⟩

theorem functionFieldMap_isIso :
    IsIso (CommRingCat.ofHom (AlgebraicGeometry.Scheme.functionFieldMap
      (projection A ell p))) := by
  change IsIso (Y.presheaf.stalkSpecializes _ ≫
    (projection A ell p).stalkMap (genericPoint (model A ell p)))
  have he : Y.presheaf.stalkSpecializes
      (specializes_of_eq (AlgebraicGeometry.Scheme.map_genericPoint_of_isDominant _
        (projection A ell p))) =
      (Y.presheaf.stalkCongr (.of_eq
        (AlgebraicGeometry.Scheme.map_genericPoint_of_isDominant _
          (projection A ell p)).symm)).hom := rfl
  rw [he]
  infer_instance

/-- The original and prime-inverted function fields are related by the actual
projection's generic stalk map, rather than by a supplied field identification. -/
def functionFieldRingEquiv : Y.functionField ≃+* (model A ell p).functionField := by
  letI := functionFieldMap_isIso A ell p
  exact (asIso (CommRingCat.ofHom
    (AlgebraicGeometry.Scheme.functionFieldMap (projection A ell p)))).commRingCatIsoToRingEquiv

@[simp] theorem functionFieldRingEquiv_apply (a : Y.functionField) :
    functionFieldRingEquiv A ell p a =
      AlgebraicGeometry.Scheme.functionFieldMap (projection A ell p) a := rfl

end FunctionField

end AlgebraicGeometry.Scheme.PrimeInversion
