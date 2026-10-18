/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.RegularList.Sheaf.Localization

/-!
# The original regular-quotient tilde-global-sections counit

The principal-basis criterion applies to the actual original closed-adjoint resolution.
Its homology sheaves are quasicoherent and concentrated in the ordered regular-list
length. The original ordered Koszul top class fixes the top quotient sheaf frame.
-/

universe u w z u1 v1 w1 r1 a b

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct ChangeOfRings

private def scalarExtensionQuotientIso {R A : Type u} [CommRing R] [CommRing A]
    (σ : R →+* A) (I : Ideal R) :
    (ModuleCat.extendScalars σ).obj (ModuleCat.of R (R ⧸ I)) ≅
      ModuleCat.of A (A ⧸ I.map σ) := by
  let : Algebra R A := σ.toAlgebra
  exact (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).symm.toLinearEquiv.toModuleIso

namespace AlgebraicGeometry.Scheme.Modules
section NativeAliases
local instance (B : CommRingCat.{u}) : (moduleSpecΓFunctor (R := B)).Additive :=
  moduleSpecΓFunctor_additive B
variable {R : CommRingCat.{u}}
private abbrev quotientSpecRing (I : Ideal R) : CommRingCat.{u} := .of (R ⧸ I)
private abbrev ambientAwayRing (t : R) : CommRingCat.{u} := .of (Localization.Away t)
private abbrev quotientAwaySpecRing (I : Ideal R) (t : R) : CommRingCat.{u} :=
  .of (Localization.Away (Ideal.Quotient.mk I t))
private abbrev quotientSpecMap (I : Ideal R) : R ⟶ quotientSpecRing I :=
  CommRingCat.ofHom (Ideal.Quotient.mk I)
private abbrev ambientAwayUnit (t : R) : R ⟶ ambientAwayRing t :=
  CommRingCat.ofHom (algebraMap R (Localization.Away t))
private abbrev quotientAwayUnit (I : Ideal R) (t : R) :
    quotientSpecRing I ⟶ quotientAwaySpecRing I t :=
  CommRingCat.ofHom (algebraMap (R ⧸ I) (Localization.Away (Ideal.Quotient.mk I t)))
private abbrev localizedQuotientSpecMap (I : Ideal R) (t : R) :
    ambientAwayRing t ⟶ quotientAwaySpecRing I t :=
  CommRingCat.ofHom (IsLocalization.Away.map (Localization.Away t)
    (Localization.Away (Ideal.Quotient.mk I t)) (Ideal.Quotient.mk I) t)
private theorem ambientAway_flat (t : R) : (ambientAwayUnit t).hom.Flat :=
  RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat (Localization.Away t) (Submonoid.powers t))
private theorem quotientLocalizationSquare (I : Ideal R) (t : R) :
    IsPullback (Spec.map (quotientAwayUnit I t)) (Spec.map (localizedQuotientSpecMap I t))
      (Spec.map (quotientSpecMap I)) (Spec.map (ambientAwayUnit t)) :=
  (Scheme.isPullback_specMap_localizationAway (quotientSpecMap I) t).flip

private abbrev scalarExtensionQuotientAwayIso (I : Ideal R) (t : R) :=
  closedImmersionQuotientLocalizationSourceIso I t
private abbrev scalarExtensionQuotientAwayIso_one_tmul (I : Ideal R) (t r : R) :=
  closedImmersionQuotientLocalizationSourceIso_one_tmul I t r

variable {A : CommRingCat.{u}}
private abbrev openRestrictedInjectiveResolution (σ : R ⟶ A)
    [IsOpenImmersion (Spec.map σ)] {L : (Spec R).Modules} (J : InjectiveResolution L) :=
  affineOpenRestrictedInjectiveResolution σ J
private theorem openRestricted_quasicoherent (σ : R ⟶ A) [IsOpenImmersion (Spec.map σ)]
    (L : (Spec R).Modules) [L.IsQuasicoherent] :
    ((restrictFunctor (Spec.map σ)).obj L).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).prop_of_iso
    ((restrictFunctorIsoPullback (Spec.map σ)).symm.app L) (isQuasicoherent_pullback σ L)
private abbrev openSpecRestrictionMap (σ : R ⟶ A) [IsOpenImmersion (Spec.map σ)]
    (L : (Spec R).Modules) := affineOpenRestrictionSectionsMap σ L
private abbrev openSpecRestrictionNat (σ : R ⟶ A) [IsOpenImmersion (Spec.map σ)] :=
  affineOpenRestrictionSectionsNat σ
private abbrev openSpecRestrictionNat_app (σ : R ⟶ A) [IsOpenImmersion (Spec.map σ)]
    (L : (Spec R).Modules) := affineOpenRestrictionSectionsNat_app σ L

private abbrev closedΓResolutionIso (q : R ⟶ A) [IsClosedImmersion (Spec.map q)]
    {L : (Spec R).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L) :=
  affineClosedRightAdjointResolutionSectionsIso q J
private abbrev closedΓResolutionIso_hom_f (q : R ⟶ A) [IsClosedImmersion (Spec.map q)]
    {L : (Spec R).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L) (n : ℕ) :=
  affineClosedRightAdjointResolutionSectionsIso_hom_f q J n
private abbrev closedΓResolutionExtAddEquiv [HasExt.{w} (ModuleCat.{u} R)]
    (q : R ⟶ A) [IsClosedImmersion (Spec.map q)] {L : (Spec R).Modules} [L.IsQuasicoherent]
    (J : InjectiveResolution L) (n : ℕ) := affineClosedRightAdjointResolutionExtAddEquiv q J n
private abbrev closedΓResolutionExtLinearEquiv [HasExt.{w} (ModuleCat.{u} R)]
    (q : R ⟶ A) [IsClosedImmersion (Spec.map q)] {L : (Spec R).Modules} [L.IsQuasicoherent]
    (J : InjectiveResolution L) (n : ℕ) := affineClosedRightAdjointResolutionExtLinearEquiv q J n
private abbrev closedΓResolutionComplex (q : R ⟶ A) [IsClosedImmersion (Spec.map q)]
    {L : (Spec R).Modules} (J : InjectiveResolution L) :=
  ((moduleSpecΓFunctor (R := A)).mapHomologicalComplex (.up ℤ)).obj
    (((closedImmersionRightAdjoint (Spec.map q)).mapHomologicalComplex (.up ℤ)).obj
      J.cochainComplex)

private abbrev quotientLocalizationGeoComplex (I : Ideal R) (t : R) {L : (Spec R).Modules}
    (J : InjectiveResolution L) := closedImmersionQuotientLocalizationResolutionMap I t J
private abbrev quotientLocalizationGeoHomology (I : Ideal R) (t : R) {L : (Spec R).Modules}
    (J : InjectiveResolution L) (n : ℤ) := closedImmersionQuotientLocalizationHomologyMap I t J n
private abbrev quotientLocalizationGeoHomology_ext (I : Ideal R) (t : R)
    [HasExt.{w} (ModuleCat.{u} R)] [HasExt.{z} (ModuleCat.{u} (Localization.Away t))]
    {L : (Spec R).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L) (n : ℕ)
    (x : (closedΓResolutionComplex (quotientSpecMap I) J).homology (n : ℤ)) :=
  closedImmersionQuotientLocalizationHomologyMap_ext I t J n x
end NativeAliases
end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
section LocalNativeAliases
variable {R : CommRingCat.{u}} (I : Ideal R) (t : R) {L : (Spec R).Modules}
local instance : IsClosedImmersion (Spec.map (localizedQuotientSpecMap I t)) :=
  Scheme.isClosedImmersion_specMap_localizationAway (quotientSpecMap I) t
private abbrev quotientLocalΓComplex (J : InjectiveResolution L) :=
  closedΓResolutionComplex (localizedQuotientSpecMap I t)
    (openRestrictedInjectiveResolution (ambientAwayUnit t) J)
private abbrev openRestrictedCochainIso (J : InjectiveResolution L) :=
  J.cocomplex.mapExtendIso (restrictFunctor (Spec.map (ambientAwayUnit t)))
    ComplexShape.embeddingUpNat
end LocalNativeAliases
end AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian HomologicalComplex CochainComplex
private def extIsoTransport {C : Type u1} [Category.{v1} C] [Abelian C] [HasExt.{w1} C]
    (R : Type r1) [CommRing R] [Linear R C] {X X' Y Y' : C}
    (eX : X' ≅ X) (eY : Y ≅ Y') (n : ℕ) : Ext X Y n ≃ₗ[R] Ext X' Y' n where
  toFun x := ((Ext.mk₀ eX.hom).comp x (zero_add n)).comp (Ext.mk₀ eY.hom) (add_zero n)
  invFun y := ((Ext.mk₀ eX.inv).comp y (zero_add n)).comp (Ext.mk₀ eY.inv) (add_zero n)
  left_inv x := by
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
      Iso.hom_inv_id, Ext.comp_mk₀_id, Ext.mk₀_comp_mk₀_assoc,
      Iso.inv_hom_id, Ext.mk₀_id_comp]
  right_inv x := by
    simp only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀,
      Iso.inv_hom_id, Ext.comp_mk₀_id, Ext.mk₀_comp_mk₀_assoc,
      Iso.hom_inv_id, Ext.mk₀_id_comp]
  map_add' x y := by simp only [Ext.comp_add, Ext.add_comp]
  map_smul' a x := by
    simp only [Ext.comp_smul, Ext.smul_comp]
    rfl

open CategoryTheory.Abelian HomologicalComplex CochainComplex
open scoped ModuleCat.Algebra
namespace AlgebraicGeometry.Scheme.Modules
section LocalLinear
variable {R : CommRingCat.{u}} (I : Ideal R) (t : R)
  {L : (Spec R).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)

local instance : IsClosedImmersion (Spec.map (localizedQuotientSpecMap I t)) :=
  Scheme.isClosedImmersion_specMap_localizationAway (quotientSpecMap I) t
local instance : (moduleSpecΓFunctor (R := quotientAwaySpecRing I t)).Additive :=
  moduleSpecΓFunctor_additive (quotientAwaySpecRing I t)
local instance : ((restrictFunctor (Spec.map (ambientAwayUnit t))).obj L).IsQuasicoherent :=
  openRestricted_quasicoherent (ambientAwayUnit t) L

variable [HasExt.{z} (ModuleCat.{u} (ambientAwayRing t))]

private def quotientLocalΓExtLinearEquiv (n : ℕ) :
    (ModuleCat.restrictScalars (quotientSpecMap I).hom).obj
      ((ModuleCat.restrictScalars (quotientAwayUnit I t).hom).obj
        ((quotientLocalΓComplex I t J).homology (n : ℤ))) ≃ₗ[R]
      Ext.{z} ((ModuleCat.restrictScalars (localizedQuotientSpecMap I t).hom).obj
        (ModuleCat.of (quotientAwaySpecRing I t) (quotientAwaySpecRing I t)))
        ((moduleSpecΓFunctor (R := ambientAwayRing t)).obj
          ((restrictFunctor (Spec.map (ambientAwayUnit t))).obj L)) n where
  __ := closedΓResolutionExtAddEquiv (localizedQuotientSpecMap I t)
    (openRestrictedInjectiveResolution (ambientAwayUnit t) J) n
  map_smul' r x := by
    let IR := AffineDerived.globalSectionsInjectiveResolution
      (openRestrictedInjectiveResolution (ambientAwayUnit t) J)
    let E := ModuleCat.coextendScalarsResolutionExtAddEquiv (localizedQuotientSpecMap I t).hom IR n
    let e := (homologyFunctor (ModuleCat.{u} (quotientAwaySpecRing I t)) (.up ℤ) (n : ℤ)).mapIso
      (closedΓResolutionIso (localizedQuotientSpecMap I t)
        (openRestrictedInjectiveResolution (ambientAwayUnit t) J))
    have hσ : (localizedQuotientSpecMap I t).hom ((ambientAwayUnit t).hom r) =
        (quotientAwayUnit I t).hom ((quotientSpecMap I).hom r) :=
      ConcreteCategory.congr_hom
        (CommRingCat.localizationAway_map_comm (quotientSpecMap I) t) r
    change E (e.hom ((quotientAwayUnit I t).hom ((quotientSpecMap I).hom r) •
        (show (quotientLocalΓComplex I t J).homology (n : ℤ) from x))) =
      r • E (e.hom x)
    rw [← hσ, e.hom.hom.map_smul, ModuleCat.coextendScalarsResolutionExtAddEquiv_smul]
    have hm : (ModuleCat.restrictScalars (localizedQuotientSpecMap I t).hom).map
        (ModuleCat.ofHom
          (X := ModuleCat.of (quotientAwaySpecRing I t) (quotientAwaySpecRing I t))
          (Y := ModuleCat.of (quotientAwaySpecRing I t) (quotientAwaySpecRing I t))
          (LinearMap.mulRight (quotientAwaySpecRing I t)
            ((localizedQuotientSpecMap I t).hom ((ambientAwayUnit t).hom r)))) =
        r • 𝟙 ((ModuleCat.restrictScalars (localizedQuotientSpecMap I t).hom).obj
          (ModuleCat.of (quotientAwaySpecRing I t) (quotientAwaySpecRing I t))) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      change (show quotientAwaySpecRing I t from y) *
          (localizedQuotientSpecMap I t).hom ((ambientAwayUnit t).hom r) =
        (localizedQuotientSpecMap I t).hom ((ambientAwayUnit t).hom r) *
          (show quotientAwaySpecRing I t from y)
      exact mul_comm _ _
    rw [hm]
    simp only [Ext.mk₀_smul, Ext.smul_comp, Ext.mk₀_id_comp]
    rfl

end LocalLinear
end AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian HomologicalComplex CochainComplex
open scoped ModuleCat.Algebra
namespace AlgebraicGeometry.Scheme.Modules
section TopLocalization
variable {R : CommRingCat.{u}} (I : Ideal R) (t : R)

local instance : PreservesFiniteLimits (ModuleCat.extendScalars (ambientAwayUnit t).hom) :=
  ModuleCat.extendScalars_preservesFiniteLimits_of_flat _ (ambientAway_flat t)
local instance : PreservesFiniteColimits (ModuleCat.extendScalars (ambientAwayUnit t).hom) :=
  ModuleCat.extendScalars_preservesFiniteColimits_of_flat _ (ambientAway_flat t)

local instance : (ModuleCat.extendScalars (ambientAwayUnit t).hom).Linear R :=
  ModuleCat.Algebra.extendScalars_linear R (Localization.Away t)

variable [HasExt.{w} (ModuleCat.{u} R)]
  [HasExt.{z} (ModuleCat.{u} (ambientAwayRing t))]

private def quotientLocalizationExtTransport (N : (Spec R).Modules) [N.IsQuasicoherent] (n : ℕ) :
    Ext.{z} ((ModuleCat.extendScalars (ambientAwayUnit t).hom).obj (ModuleCat.of R (R ⧸ I)))
        ((ModuleCat.extendScalars (ambientAwayUnit t).hom).obj (moduleSpecΓFunctor.obj N)) n ≃ₗ[R]
      Ext.{z} ((ModuleCat.restrictScalars (localizedQuotientSpecMap I t).hom).obj
        (ModuleCat.of (quotientAwaySpecRing I t) (quotientAwaySpecRing I t)))
        ((moduleSpecΓFunctor (R := ambientAwayRing t)).obj
          ((restrictFunctor (Spec.map (ambientAwayUnit t))).obj N)) n := by
  exact extIsoTransport R (scalarExtensionQuotientAwayIso I t).symm
    (affineRestrictGlobalSectionsIso (ambientAwayUnit t) N) n

private def quotientLocalizationExtLinearMap (N : (Spec R).Modules) [N.IsQuasicoherent] (n : ℕ) :
    Ext.{w} (ModuleCat.of R (R ⧸ I)) (moduleSpecΓFunctor.obj N) n →ₗ[R]
      Ext.{z} ((ModuleCat.restrictScalars (localizedQuotientSpecMap I t).hom).obj
        (ModuleCat.of (quotientAwaySpecRing I t) (quotientAwaySpecRing I t)))
        ((moduleSpecΓFunctor (R := ambientAwayRing t)).obj
          ((restrictFunctor (Spec.map (ambientAwayUnit t))).obj N)) n :=
  (quotientLocalizationExtTransport I t N n).toLinearMap.comp
    ((ModuleCat.extendScalars (ambientAwayUnit t).hom).mapExtLinearMap R
      (ModuleCat.of R (R ⧸ I)) (moduleSpecΓFunctor.obj N) n)

private theorem quotientLocalizationExt_isLocalized (s : List R)
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (N : (Spec R).Modules) [N.IsQuasicoherent] :
    IsLocalizedModule (Submonoid.powers t)
      (quotientLocalizationExtLinearMap (Ideal.ofList s) t N s.length) := by
  let b := (ModuleCat.extendScalars (ambientAwayUnit t).hom).mapExtLinearMap R
    (ModuleCat.of R (R ⧸ Ideal.ofList s)) (moduleSpecΓFunctor.obj N) s.length
  let : IsLocalizedModule (Submonoid.powers t) b :=
    ChainComplex.Koszul.topExtScalarExtension_isLocalizedModule
      (A := Localization.Away t) (Submonoid.powers t) s hs (moduleSpecΓFunctor.obj N)
  exact IsLocalizedModule.of_linearEquiv (Submonoid.powers t) b
    (quotientLocalizationExtTransport (Ideal.ofList s) t N s.length)

end TopLocalization
end AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian HomologicalComplex CochainComplex
open scoped ModuleCat.Algebra
namespace AlgebraicGeometry.Scheme.Modules
section GeometricLocalization
variable {R : CommRingCat.{u}} (s : List R)
  (hs : RingTheory.Sequence.IsWeaklyRegular R s) (t : R)
  {L : (Spec R).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)

local instance : IsClosedImmersion
    (Spec.map (localizedQuotientSpecMap (Ideal.ofList s) t)) :=
  Scheme.isClosedImmersion_specMap_localizationAway (quotientSpecMap (Ideal.ofList s)) t
local instance : (moduleSpecΓFunctor (R := quotientAwaySpecRing (Ideal.ofList s) t)).Additive :=
  moduleSpecΓFunctor_additive (quotientAwaySpecRing (Ideal.ofList s) t)
local instance : ((restrictFunctor (Spec.map (ambientAwayUnit t))).obj L).IsQuasicoherent :=
  openRestricted_quasicoherent (ambientAwayUnit t) L
local instance : PreservesFiniteLimits (ModuleCat.extendScalars (ambientAwayUnit t).hom) :=
  ModuleCat.extendScalars_preservesFiniteLimits_of_flat _ (ambientAway_flat t)
local instance : PreservesFiniteColimits (ModuleCat.extendScalars (ambientAwayUnit t).hom) :=
  ModuleCat.extendScalars_preservesFiniteColimits_of_flat _ (ambientAway_flat t)
local instance : (ModuleCat.extendScalars (ambientAwayUnit t).hom).Linear R :=
  ModuleCat.Algebra.extendScalars_linear R (Localization.Away t)

variable [HasExt.{w} (ModuleCat.{u} R)]
  [HasExt.{z} (ModuleCat.{u} (ambientAwayRing t))]

include hs in
private theorem quotientLocalizationGeoHomology_top_isLocalized_R :
    IsLocalizedModule (Submonoid.powers t)
      (((ModuleCat.restrictScalars (quotientSpecMap (Ideal.ofList s)).hom).map
        (quotientLocalizationGeoHomology (Ideal.ofList s) t J (s.length : ℤ))).hom) := by
  let b := quotientLocalizationExtLinearMap (Ideal.ofList s) t L s.length
  let E := closedΓResolutionExtLinearEquiv (quotientSpecMap (Ideal.ofList s)) J s.length
  let E' := quotientLocalΓExtLinearEquiv (Ideal.ofList s) t J s.length
  let f := (ModuleCat.restrictScalars (quotientSpecMap (Ideal.ofList s)).hom).map
    (quotientLocalizationGeoHomology (Ideal.ofList s) t J (s.length : ℤ))
  have he : f.hom = E'.symm.toLinearMap.comp (b.comp E.toLinearMap) := by
    apply LinearMap.ext
    intro x
    apply E'.injective
    change E' (f x) = E' (E'.symm (b (E x)))
    rw [E'.apply_symm_apply]
    exact quotientLocalizationGeoHomology_ext (Ideal.ofList s) t J s.length x
  let : IsLocalizedModule (Submonoid.powers t) b :=
    quotientLocalizationExt_isLocalized t s hs L
  let : IsLocalizedModule (Submonoid.powers t) (b.comp E.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right (Submonoid.powers t) b E
  have h : IsLocalizedModule (Submonoid.powers t)
      (E'.symm.toLinearMap.comp (b.comp E.toLinearMap)) :=
    IsLocalizedModule.of_linearEquiv (Submonoid.powers t) (b.comp E.toLinearMap) E'.symm
  change IsLocalizedModule (Submonoid.powers t) f.hom
  rw [he]
  exact h

include hs in
private theorem quotientLocalizationGeoHomology_top_isLocalized :
    IsLocalizedModule (Submonoid.powers (Ideal.Quotient.mk (Ideal.ofList s) t))
      (quotientLocalizationGeoHomology (Ideal.ofList s) t J (s.length : ℤ)).hom := by
  let f := (quotientLocalizationGeoHomology (Ideal.ofList s) t J (s.length : ℤ)).hom
  let : IsLocalizedModule (Submonoid.powers t) (f.restrictScalars R) :=
    quotientLocalizationGeoHomology_top_isLocalized_R s hs t J
  have h := IsLocalizedModule.of_restrictScalars (A := R ⧸ Ideal.ofList s)
    (Submonoid.powers t) f
  simpa only [Algebra.algebraMapSubmonoid_powers, Ideal.Quotient.algebraMap_eq] using h

end GeometricLocalization
end AlgebraicGeometry.Scheme.Modules

open HomologicalComplex Opposite
namespace AlgebraicGeometry.Scheme.Modules
section OpenSections
variable {R A : CommRingCat.{u}} (σ : R ⟶ A) [IsOpenImmersion (Spec.map σ)]

private theorem open_unit_sections_isIso (N : (Spec R).Modules) :
    IsIso ((Complex.specSectionsFunctor R (Spec.map σ).opensRange).map
      ((restrictAdjunction (Spec.map σ)).unit.app N)) := by
  let j := Spec.map σ
  have he : j ''ᵁ (j ⁻¹ᵁ j.opensRange) = j.opensRange := by
    rw [Scheme.Hom.preimage_opensRange, j.image_top_eq_opensRange]
  have hι : IsIso ((restrictAdjunction j).unit.app N |>.app j.opensRange) := by
    rw [restrictAdjunction_unit_app_app]
    have hh : homOfLE (j.image_preimage_le j.opensRange) = eqToHom he := Subsingleton.elim _ _
    rw [hh]
    infer_instance
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ConcreteCategory.bijective_of_isIso (((restrictAdjunction j).unit.app N).app j.opensRange)

private theorem open_pushforward_sections_isIso (N : (Spec A).Modules) :
    IsIso ((Complex.specSectionsRestriction R (Spec.map σ).opensRange).app
      ((pushforward (Spec.map σ)).obj N)) := by
  let j := Spec.map σ
  have he : j ⁻¹ᵁ (⊤ : (Spec R).Opens) = j ⁻¹ᵁ j.opensRange := by
    rw [Scheme.Hom.preimage_opensRange]
    rfl
  have hh : (TopologicalSpace.Opens.map j.base).map (homOfLE (show j.opensRange ≤ ⊤ from le_top)) =
      eqToHom he.symm := Subsingleton.elim _ _
  have hι : IsIso (((pushforward j).obj N).presheaf.map
      (homOfLE (show j.opensRange ≤ ⊤ from le_top)).op) := by
    rw [pushforward_obj_presheaf_map, hh]
    infer_instance
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact ConcreteCategory.bijective_of_isIso
    (((pushforward j).obj N).presheaf.map
      (homOfLE (show j.opensRange ≤ ⊤ from le_top)).op)

private def openSpecSectionsIsoApp (N : (Spec R).Modules) :
    (ModuleCat.restrictScalars σ.hom).obj
        ((moduleSpecΓFunctor (R := A)).obj ((restrictFunctor (Spec.map σ)).obj N)) ≅
      (Complex.specSectionsFunctor R (Spec.map σ).opensRange).obj N := by
  letI := open_pushforward_sections_isIso σ ((restrictFunctor (Spec.map σ)).obj N)
  letI := open_unit_sections_isIso σ N
  exact ((pushforwardGlobalSectionsIso σ).app ((restrictFunctor (Spec.map σ)).obj N)).symm ≪≫
    asIso ((Complex.specSectionsRestriction R (Spec.map σ).opensRange).app
      ((pushforward (Spec.map σ)).obj ((restrictFunctor (Spec.map σ)).obj N))) ≪≫
    (asIso ((Complex.specSectionsFunctor R (Spec.map σ).opensRange).map
      ((restrictAdjunction (Spec.map σ)).unit.app N))).symm

private theorem openSpecSectionsIsoApp_unit (N : (Spec R).Modules) :
    openSpecRestrictionMap σ N ≫ (openSpecSectionsIsoApp σ N).hom =
      (Complex.specSectionsRestriction R (Spec.map σ).opensRange).app N := by
  let := open_unit_sections_isIso σ N
  dsimp only [openSpecRestrictionMap, affineOpenRestrictionSectionsMap, openSpecSectionsIsoApp,
    Iso.trans_hom,
    Iso.symm_hom, asIso_hom, asIso_inv]
  simp only [Category.assoc]
  have hpair : (pushforwardGlobalSectionsIso σ).hom.app
        ((restrictFunctor (Spec.map σ)).obj N) ≫
      ((pushforwardGlobalSectionsIso σ).app ((restrictFunctor (Spec.map σ)).obj N)).inv = 𝟙 _ :=
    ((pushforwardGlobalSectionsIso σ).app ((restrictFunctor (Spec.map σ)).obj N)).hom_inv_id
  rw [reassoc_of% hpair]
  rw [← Category.assoc]
  calc
    _ = ((Complex.specSectionsRestriction R (Spec.map σ).opensRange).app N ≫
        (Complex.specSectionsFunctor R (Spec.map σ).opensRange).map
          ((restrictAdjunction (Spec.map σ)).unit.app N)) ≫
        inv ((Complex.specSectionsFunctor R (Spec.map σ).opensRange).map
          ((restrictAdjunction (Spec.map σ)).unit.app N)) :=
      congrArg (fun p => p ≫ inv ((Complex.specSectionsFunctor R (Spec.map σ).opensRange).map
        ((restrictAdjunction (Spec.map σ)).unit.app N)))
        ((Complex.specSectionsRestriction R (Spec.map σ).opensRange).naturality
          ((restrictAdjunction (Spec.map σ)).unit.app N))
    _ = _ := by simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

private def openUnitSectionsNat :
    Complex.specSectionsFunctor R (Spec.map σ).opensRange ⟶
      (restrictFunctor (Spec.map σ) ⋙ pushforward (Spec.map σ)) ⋙
        Complex.specSectionsFunctor R (Spec.map σ).opensRange :=
  (Functor.leftUnitor (Complex.specSectionsFunctor R (Spec.map σ).opensRange)).inv ≫
    Functor.whiskerRight (restrictAdjunction (Spec.map σ)).unit
      (Complex.specSectionsFunctor R (Spec.map σ).opensRange)

private theorem openUnitSectionsNat_app (N : (Spec R).Modules) :
    (openUnitSectionsNat σ).app N =
      (Complex.specSectionsFunctor R (Spec.map σ).opensRange).map
        ((restrictAdjunction (Spec.map σ)).unit.app N) := by
  simp only [openUnitSectionsNat, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Category.id_comp]

private def openSpecSectionsIso :
    restrictFunctor (Spec.map σ) ⋙ moduleSpecΓFunctor (R := A) ⋙
        ModuleCat.restrictScalars σ.hom ≅
      Complex.specSectionsFunctor R (Spec.map σ).opensRange := by
  let δ := Functor.whiskerLeft (restrictFunctor (Spec.map σ) ⋙ pushforward (Spec.map σ))
    (Complex.specSectionsRestriction R (Spec.map σ).opensRange)
  let η := openUnitSectionsNat σ
  letI : ∀ N, IsIso (δ.app N) := fun N =>
    open_pushforward_sections_isIso σ ((restrictFunctor (Spec.map σ)).obj N)
  letI : IsIso δ := NatIso.isIso_of_isIso_app δ
  letI : ∀ N, IsIso (η.app N) := fun N => by
    rw [openUnitSectionsNat_app]
    exact open_unit_sections_isIso σ N
  letI : IsIso η := NatIso.isIso_of_isIso_app η
  exact Functor.isoWhiskerLeft (restrictFunctor (Spec.map σ)) (pushforwardGlobalSectionsIso
    σ).symm ≪≫
    (Functor.associator (restrictFunctor (Spec.map σ)) (pushforward (Spec.map σ))
      (moduleSpecΓFunctor (R := R))).symm ≪≫
    asIso δ ≪≫ (asIso η).symm

private theorem openSpecSectionsIso_hom_app (N : (Spec R).Modules) :
    (openSpecSectionsIso σ).hom.app N = (openSpecSectionsIsoApp σ N).hom := by
  dsimp only [openSpecSectionsIso, openSpecSectionsIsoApp, Iso.trans_hom, Iso.symm_hom]
  simp only [NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_inv_app, asIso_hom, asIso_inv, NatIso.isIso_inv_app,
    Functor.whiskerLeft_app, Category.id_comp,
    openUnitSectionsNat_app]
  rfl

private theorem openSpecSectionsIso_unit (N : (Spec R).Modules) :
    openSpecRestrictionMap σ N ≫ (openSpecSectionsIso σ).hom.app N =
      (Complex.specSectionsRestriction R (Spec.map σ).opensRange).app N := by
  rw [openSpecSectionsIso_hom_app]
  exact openSpecSectionsIsoApp_unit σ N

private def openSpecRestrictionComplex (K : CochainComplex (Spec R).Modules ℤ) :
    ((moduleSpecΓFunctor (R := R)).mapHomologicalComplex (.up ℤ)).obj K ⟶
      ((ModuleCat.restrictScalars σ.hom).mapHomologicalComplex (.up ℤ)).obj
        (((moduleSpecΓFunctor (R := A)).mapHomologicalComplex (.up ℤ)).obj
          (((restrictFunctor (Spec.map σ)).mapHomologicalComplex (.up ℤ)).obj K)) where
  f n := openSpecRestrictionMap σ (K.X n)
  comm' n m _ := ((openSpecRestrictionNat σ).naturality (K.d n m)).symm

private def openSpecSectionsComplexIso (K : CochainComplex (Spec R).Modules ℤ) :
    ((ModuleCat.restrictScalars σ.hom).mapHomologicalComplex (.up ℤ)).obj
        (((moduleSpecΓFunctor (R := A)).mapHomologicalComplex (.up ℤ)).obj
          (((restrictFunctor (Spec.map σ)).mapHomologicalComplex (.up ℤ)).obj K)) ≅
      ((Complex.specSectionsFunctor R (Spec.map σ).opensRange).mapHomologicalComplex (.up ℤ)).obj
        K :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (openSpecSectionsIso σ).app (K.X n))
    (by intro n m _; exact ((openSpecSectionsIso σ).hom.naturality (K.d n m)).symm)

private theorem openSpecSectionsComplexIso_unit (K : CochainComplex (Spec R).Modules ℤ) :
    openSpecRestrictionComplex σ K ≫ (openSpecSectionsComplexIso σ K).hom =
      Complex.specSectionsComplexRestriction R (.up ℤ) (Spec.map σ).opensRange K := by
  ext n : 1
  exact openSpecSectionsIso_unit σ (K.X n)

end OpenSections
end AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian HomologicalComplex CochainComplex
namespace AlgebraicGeometry.Scheme.Modules
section PrincipalModel
variable {R : CommRingCat.{u}} (I : Ideal R) (t : R)
  {L : (Spec R).Modules} (J : InjectiveResolution L)

local instance : IsClosedImmersion (Spec.map (localizedQuotientSpecMap I t)) :=
  Scheme.isClosedImmersion_specMap_localizationAway (quotientSpecMap I) t
local instance : (moduleSpecΓFunctor (R := quotientAwaySpecRing I t)).Additive :=
  moduleSpecΓFunctor_additive (quotientAwaySpecRing I t)

private def quotientAfterOpenCochainIso :
    ((restrictFunctor (Spec.map (quotientAwayUnit I t))).mapHomologicalComplex (.up ℤ)).obj
        (((closedImmersionRightAdjoint (Spec.map (quotientSpecMap I))).mapHomologicalComplex
          (.up ℤ)).obj J.cochainComplex) ≅
      ((closedImmersionRightAdjoint (Spec.map (localizedQuotientSpecMap I t))).mapHomologicalComplex
        (.up ℤ)).obj (openRestrictedInjectiveResolution (ambientAwayUnit t) J).cochainComplex :=
  (Functor.mapHomologicalComplexCompIso
      (closedImmersionRightAdjointOpenIso (Spec.map (quotientAwayUnit I t))
        (Spec.map (localizedQuotientSpecMap I t)) (Spec.map (quotientSpecMap I))
        (Spec.map (ambientAwayUnit t)) (quotientLocalizationSquare I t)) (.up ℤ)).app
          J.cochainComplex ≪≫
    ((Functor.mapHomologicalComplexCompIso
      (Iso.refl (restrictFunctor (Spec.map (ambientAwayUnit t)) ⋙
        closedImmersionRightAdjoint (Spec.map (localizedQuotientSpecMap I t))))
      (.up ℤ)).app J.cochainComplex).symm ≪≫
    ((closedImmersionRightAdjoint (Spec.map (localizedQuotientSpecMap I t))).mapHomologicalComplex
      (.up ℤ)).mapIso (openRestrictedCochainIso t J)

private def quotientAfterOpenSectionsIso :
    ((ModuleCat.restrictScalars (quotientAwayUnit I t).hom).mapHomologicalComplex (.up ℤ)).obj
      (((moduleSpecΓFunctor (R := quotientAwaySpecRing I t)).mapHomologicalComplex (.up ℤ)).obj
        (((restrictFunctor (Spec.map (quotientAwayUnit I t))).mapHomologicalComplex (.up ℤ)).obj
          (((closedImmersionRightAdjoint (Spec.map (quotientSpecMap I))).mapHomologicalComplex
            (.up ℤ)).obj J.cochainComplex))) ≅
      ((ModuleCat.restrictScalars (quotientAwayUnit I t).hom).mapHomologicalComplex (.up ℤ)).obj
        (quotientLocalΓComplex I t J) :=
  ((ModuleCat.restrictScalars (quotientAwayUnit I t).hom).mapHomologicalComplex (.up ℤ)).mapIso
    (((moduleSpecΓFunctor (R := quotientAwaySpecRing I t)).mapHomologicalComplex (.up ℤ)).mapIso
      (quotientAfterOpenCochainIso I t J))

private theorem quotientLocalizationGeoComplex_factor :
    quotientLocalizationGeoComplex I t J =
      openSpecRestrictionComplex (quotientAwayUnit I t)
          (((closedImmersionRightAdjoint (Spec.map (quotientSpecMap I))).mapHomologicalComplex
            (.up ℤ)).obj J.cochainComplex) ≫
        (quotientAfterOpenSectionsIso I t J).hom := by
  ext n : 1
  dsimp only [quotientLocalizationGeoComplex]
  rw [closedImmersionQuotientLocalizationResolutionMap_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

end PrincipalModel
end AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian HomologicalComplex CochainComplex
namespace AlgebraicGeometry.Scheme.Modules
section RegularConcentration
variable {R : CommRingCat.{u}} (s : List R)
  (hs : RingTheory.Sequence.IsWeaklyRegular R s) (t : R)
  {L : (Spec R).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)
  (e : (moduleSpecΓFunctor (R := R)).obj L ≅ ModuleCat.of R R)

local instance : IsClosedImmersion
    (Spec.map (localizedQuotientSpecMap (Ideal.ofList s) t)) :=
  Scheme.isClosedImmersion_specMap_localizationAway (quotientSpecMap (Ideal.ofList s)) t
local instance : (moduleSpecΓFunctor (R := quotientSpecRing (Ideal.ofList s))).Additive :=
  moduleSpecΓFunctor_additive (quotientSpecRing (Ideal.ofList s))
local instance : (moduleSpecΓFunctor (R := quotientAwaySpecRing (Ideal.ofList s) t)).Additive :=
  moduleSpecΓFunctor_additive (quotientAwaySpecRing (Ideal.ofList s) t)
local instance : ((restrictFunctor (Spec.map (ambientAwayUnit t))).obj L).IsQuasicoherent :=
  openRestricted_quasicoherent (ambientAwayUnit t) L

private def localRegularSourceIso :
    (ModuleCat.restrictScalars (localizedQuotientSpecMap (Ideal.ofList s) t).hom).obj
        (ModuleCat.of (quotientAwaySpecRing (Ideal.ofList s) t)
          (quotientAwaySpecRing (Ideal.ofList s) t)) ≅
      ModuleCat.of (Localization.Away t)
        (Localization.Away t ⧸ Ideal.ofList (s.map (algebraMap R (Localization.Away t)))) := by
  let E : (ModuleCat.restrictScalars (localizedQuotientSpecMap (Ideal.ofList s) t).hom).obj
      (ModuleCat.of (quotientAwaySpecRing (Ideal.ofList s) t)
        (quotientAwaySpecRing (Ideal.ofList s) t)) ≅
      ModuleCat.of (Localization.Away t)
        (Localization.Away t ⧸ (Ideal.ofList s).map (algebraMap R (Localization.Away t))) :=
    (scalarExtensionQuotientAwayIso (Ideal.ofList s) t).symm ≪≫
      scalarExtensionQuotientIso (algebraMap R (Localization.Away t)) (Ideal.ofList s)
  exact E ≪≫ eqToIso (congrArg
    (fun K : Ideal (Localization.Away t) =>
      ModuleCat.of (Localization.Away t) (Localization.Away t ⧸ K))
    (Ideal.map_ofList (algebraMap R (Localization.Away t)) s))

private def localCoefficientFrame :
    (moduleSpecΓFunctor (R := ambientAwayRing t)).obj
        ((restrictFunctor (Spec.map (ambientAwayUnit t))).obj L) ≅
      ModuleCat.of (Localization.Away t) (Localization.Away t) := by
  exact (affineRestrictGlobalSectionsIso (ambientAwayUnit t) L).symm ≪≫
    (ModuleCat.extendScalars (ambientAwayUnit t).hom).mapIso e ≪≫
    ModuleCat.extendScalarsAlgebraObjIso R (Localization.Away t) (ModuleCat.of R R) ≪≫
    (TensorProduct.AlgebraTensorModule.rid R (Localization.Away t) (Localization.Away
      t)).toModuleIso

variable [HasExt.{w} (ModuleCat.{u} R)]

include hs e in
private theorem closedΓResolutionRegular_isZero (n : ℤ) (hn : n ≠ (s.length : ℤ)) :
    IsZero ((closedΓResolutionComplex (quotientSpecMap (Ideal.ofList s)) J).homology n) := by
  by_cases hneg : n < 0
  · exact ShortComplex.isZero_homology_of_isZero_X₂ _
      ((moduleSpecΓFunctor (R := quotientSpecRing (Ideal.ofList s))).map_isZero
        ((closedImmersionRightAdjoint (Spec.map (quotientSpecMap (Ideal.ofList s)))).map_isZero
          (J.cochainComplex.isZero_of_isStrictlyGE 0 n hneg)))
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hneg)
    have hq : q ≠ s.length := by exact_mod_cast hn
    let E := closedΓResolutionExtAddEquiv (quotientSpecMap (Ideal.ofList s)) J q
    let T := extIsoTransport R (Iso.refl (ModuleCat.of R (R ⧸ Ideal.ofList s))) e q
    apply ModuleCat.isZero_iff_subsingleton.mpr
    constructor
    intro x y
    apply E.injective
    apply T.injective
    exact (ModuleCat.regularListQuotientExt_eq_zero_of_ne_length s hs q hq (T (E x))).trans
      (ModuleCat.regularListQuotientExt_eq_zero_of_ne_length s hs q hq (T (E y))).symm

variable [HasExt.{z} (ModuleCat.{u} (ambientAwayRing t))]

omit [HasExt.{w} (ModuleCat.{u} R)] in
include hs e in
private theorem quotientLocalΓRegular_isZero (n : ℤ) (hn : n ≠ (s.length : ℤ)) :
    IsZero ((quotientLocalΓComplex (Ideal.ofList s) t J).homology n) := by
  by_cases hneg : n < 0
  · exact ShortComplex.isZero_homology_of_isZero_X₂ _
      ((moduleSpecΓFunctor (R := quotientAwaySpecRing (Ideal.ofList s) t)).map_isZero
        ((closedImmersionRightAdjoint
          (Spec.map (localizedQuotientSpecMap (Ideal.ofList s) t))).map_isZero
          ((openRestrictedInjectiveResolution (ambientAwayUnit t)
            J).cochainComplex.isZero_of_isStrictlyGE
            0 n hneg)))
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hneg)
    have hq : q ≠ (s.map (algebraMap R (Localization.Away t))).length := by
      simpa only [List.length_map] using (show q ≠ s.length from by exact_mod_cast hn)
    have hsA := hs.of_isLocalization (Localization.Away t) (Submonoid.powers t)
    let E := closedΓResolutionExtAddEquiv (localizedQuotientSpecMap (Ideal.ofList s) t)
      (openRestrictedInjectiveResolution (ambientAwayUnit t) J) q
    let T := extIsoTransport (Localization.Away t) (localRegularSourceIso s t).symm
      (localCoefficientFrame t e) q
    apply ModuleCat.isZero_iff_subsingleton.mpr
    constructor
    intro x y
    apply E.injective
    apply T.injective
    exact (ModuleCat.regularListQuotientExt_eq_zero_of_ne_length _ hsA q hq (T (E x))).trans
      (ModuleCat.regularListQuotientExt_eq_zero_of_ne_length _ hsA q hq (T (E y))).symm

end RegularConcentration
end AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian HomologicalComplex CochainComplex
private theorem localized_homologyMap_of_postIso {B : Type u} [CommRing B]
    (T : Submonoid B) {K L M : CochainComplex (ModuleCat.{u} B) ℤ}
    (f : K ⟶ L) (e : L ≅ M) (n : ℤ)
    (h : IsLocalizedModule T (homologyMap (f ≫ e.hom) n).hom) :
    IsLocalizedModule T (homologyMap f n).hom := by
  let eH := (homologyFunctor (ModuleCat.{u} B) (.up ℤ) n).mapIso e
  have hcomp : IsLocalizedModule T (eH.hom.hom.comp (homologyMap f n).hom) := by
    rw [homologyMap_comp] at h
    exact h
  exact (IsLocalizedModule.comp_iff_of_bijective_left T eH.hom.hom
    (ConcreteCategory.bijective_of_isIso eH.hom)).mp hcomp

private theorem localized_homologyMap_of_restrictComparison {B A : Type u}
    [CommRing B] [CommRing A] (σ : B →+* A) (T : Submonoid B)
    (K : CochainComplex (ModuleCat.{u} B) ℤ) (C : CochainComplex (ModuleCat.{u} A) ℤ)
    (f : K ⟶ ((ModuleCat.restrictScalars σ).mapHomologicalComplex (.up ℤ)).obj C) (n : ℤ)
    (h : IsLocalizedModule T
      ((homologyMap f n ≫ ((C.sc n).mapHomologyIso (ModuleCat.restrictScalars σ)).hom).hom)) :
    IsLocalizedModule T (homologyMap f n).hom := by
  let e := (C.sc n).mapHomologyIso (ModuleCat.restrictScalars σ)
  exact (IsLocalizedModule.comp_iff_of_bijective_left T e.hom.hom
    (ConcreteCategory.bijective_of_isIso e.hom)).mp h

namespace AlgebraicGeometry.Scheme.Modules
section OpenSectionHomology
variable {B A : CommRingCat.{u}} (σ : B ⟶ A) [IsOpenImmersion (Spec.map σ)]

private def specSectionsComplexIsoOfEq (K : CochainComplex (Spec B).Modules ℤ)
    {U V : (Spec B).Opens} (h : U = V) :
    ((Complex.specSectionsFunctor B U).mapHomologicalComplex (.up ℤ)).obj K ≅
      ((Complex.specSectionsFunctor B V).mapHomologicalComplex (.up ℤ)).obj K :=
  eqToIso (congrArg
    (fun W => ((Complex.specSectionsFunctor B W).mapHomologicalComplex (.up ℤ)).obj K) h)

private theorem specSectionsComplexIsoOfEq_unit (K : CochainComplex (Spec B).Modules ℤ)
    {U V : (Spec B).Opens} (h : U = V) :
    Complex.specSectionsComplexRestriction B (.up ℤ) U K ≫
        (specSectionsComplexIsoOfEq K h).hom =
      Complex.specSectionsComplexRestriction B (.up ℤ) V K := by
  subst V
  simp only [specSectionsComplexIsoOfEq, eqToIso_refl, Iso.refl_hom, Category.comp_id]

private def specSectionsHomologyLocalizes (K : CochainComplex (Spec B).Modules ℤ)
    (U : (Spec B).Opens) (T : Submonoid B) (n : ℤ) : Prop :=
  IsLocalizedModule T
    (((homologyFunctor (ModuleCat.{u} B) (.up ℤ) n).map
      (Complex.specSectionsComplexRestriction B (.up ℤ) U K)).hom)

private theorem openSpecSectionsHomology_isLocalized (K : CochainComplex (Spec B).Modules ℤ)
    (U : (Spec B).Opens) (hU : (Spec.map σ).opensRange = U)
    (T : Submonoid B) (n : ℤ)
    (h : IsLocalizedModule T (homologyMap (openSpecRestrictionComplex σ K) n).hom) :
    specSectionsHomologyLocalizes K U T n := by
  let : IsLocalizedModule T (homologyMap (openSpecRestrictionComplex σ K) n).hom := h
  let o := openSpecSectionsComplexIso σ K ≪≫ specSectionsComplexIsoOfEq K hU
  let e := (homologyFunctor (ModuleCat.{u} B) (.up ℤ) n).mapIso o
  have h' := IsLocalizedModule.of_linearEquiv T
    (homologyMap (openSpecRestrictionComplex σ K) n).hom e.toLinearEquiv
  have hh : openSpecRestrictionComplex σ K ≫ o.hom =
      Complex.specSectionsComplexRestriction B (.up ℤ) U K := by
    change openSpecRestrictionComplex σ K ≫ (openSpecSectionsComplexIso σ K).hom ≫
      (specSectionsComplexIsoOfEq K hU).hom = _
    rw [← Category.assoc, openSpecSectionsComplexIso_unit, specSectionsComplexIsoOfEq_unit]
  change IsLocalizedModule T
    ((homologyMap (openSpecRestrictionComplex σ K) n ≫ homologyMap o.hom n).hom) at h'
  rw [← homologyMap_comp, hh] at h'
  exact h'

end OpenSectionHomology
end AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian HomologicalComplex CochainComplex
namespace AlgebraicGeometry.Scheme.Modules
section ActualCounit
variable {R : CommRingCat.{u}} (s : List R)
  (hs : RingTheory.Sequence.IsWeaklyRegular R s) (t : R)
  {L : (Spec R).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)
  (e : (moduleSpecΓFunctor (R := R)).obj L ≅ ModuleCat.of R R)

local instance : IsClosedImmersion
    (Spec.map (localizedQuotientSpecMap (Ideal.ofList s) t)) :=
  Scheme.isClosedImmersion_specMap_localizationAway (quotientSpecMap (Ideal.ofList s)) t
local instance : (moduleSpecΓFunctor (R := quotientSpecRing (Ideal.ofList s))).Additive :=
  moduleSpecΓFunctor_additive (quotientSpecRing (Ideal.ofList s))
local instance : (moduleSpecΓFunctor (R := quotientAwaySpecRing (Ideal.ofList s) t)).Additive :=
  moduleSpecΓFunctor_additive (quotientAwaySpecRing (Ideal.ofList s) t)

variable [HasExt.{w} (ModuleCat.{u} R)]
  [HasExt.{z} (ModuleCat.{u} (ambientAwayRing t))]

include hs e in
private theorem quotientLocalizationGeoHomology_isLocalized (n : ℤ) :
    IsLocalizedModule (Submonoid.powers (Ideal.Quotient.mk (Ideal.ofList s) t))
      (quotientLocalizationGeoHomology (Ideal.ofList s) t J n).hom := by
  by_cases hn : n = (s.length : ℤ)
  · subst n
    exact quotientLocalizationGeoHomology_top_isLocalized s hs t J
  · let : Subsingleton ((closedΓResolutionComplex (quotientSpecMap (Ideal.ofList s)) J).homology
    n) :=
      ModuleCat.subsingleton_of_isZero (closedΓResolutionRegular_isZero s hs J e n hn)
    let : Subsingleton ((ModuleCat.restrictScalars (quotientAwayUnit (Ideal.ofList s) t).hom).obj
        ((quotientLocalΓComplex (Ideal.ofList s) t J).homology n)) :=
      ModuleCat.subsingleton_of_isZero
        ((ModuleCat.restrictScalars (quotientAwayUnit (Ideal.ofList s) t).hom).map_isZero
          (quotientLocalΓRegular_isZero s hs t J e n hn))
    refine ⟨?_, ?_, ?_⟩
    · intro a
      apply (Module.End.isUnit_iff _).mpr
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
    · intro y
      exact ⟨⟨0, 1⟩, Subsingleton.elim _ _⟩
    · intro x y h
      exact ⟨1, Subsingleton.elim _ _⟩

private def regularClosedResolutionComplex :
    CochainComplex (Spec (quotientSpecRing (Ideal.ofList s))).Modules ℤ :=
  ((closedImmersionRightAdjoint (Spec.map (quotientSpecMap (Ideal.ofList s)))).mapHomologicalComplex
    (.up ℤ)).obj J.cochainComplex

include hs e in
private theorem quotientLocalizationOpenHomology_isLocalized (n : ℤ) :
    IsLocalizedModule (Submonoid.powers (Ideal.Quotient.mk (Ideal.ofList s) t))
      (homologyMap (openSpecRestrictionComplex (quotientAwayUnit (Ideal.ofList s) t)
        (regularClosedResolutionComplex s J)) n).hom := by
  let K := ((closedImmersionRightAdjoint (Spec.map (quotientSpecMap (Ideal.ofList
    s)))).mapHomologicalComplex
    (.up ℤ)).obj J.cochainComplex
  let β := openSpecRestrictionComplex (quotientAwayUnit (Ideal.ofList s) t) K
  let a := quotientAfterOpenSectionsIso (Ideal.ofList s) t J
  have hfa : β ≫ a.hom = quotientLocalizationGeoComplex (Ideal.ofList s) t J :=
    (quotientLocalizationGeoComplex_factor (Ideal.ofList s) t J).symm
  change IsLocalizedModule (Submonoid.powers (Ideal.Quotient.mk (Ideal.ofList s) t))
    (homologyMap β n).hom
  apply localized_homologyMap_of_postIso
    (Submonoid.powers (Ideal.Quotient.mk (Ideal.ofList s) t)) β a n
  rw [hfa]
  exact localized_homologyMap_of_restrictComparison (quotientAwayUnit (Ideal.ofList s) t).hom
    (Submonoid.powers (Ideal.Quotient.mk (Ideal.ofList s) t))
    (closedΓResolutionComplex (quotientSpecMap (Ideal.ofList s)) J)
    (quotientLocalΓComplex (Ideal.ofList s) t J)
    (quotientLocalizationGeoComplex (Ideal.ofList s) t J) n
    (by simpa only [quotientLocalizationGeoHomology,
      closedImmersionQuotientLocalizationHomologyMap_eq] using
        quotientLocalizationGeoHomology_isLocalized s hs t J e n)

include hs e in
private theorem quotientResolutionPrincipalSections_isLocalized (n : ℤ) :
    specSectionsHomologyLocalizes (regularClosedResolutionComplex s J)
      (PrimeSpectrum.basicOpen (Ideal.Quotient.mk (Ideal.ofList s) t))
      (Submonoid.powers (Ideal.Quotient.mk (Ideal.ofList s) t)) n := by
  let σ := quotientAwayUnit (Ideal.ofList s) t
  have ho : (Spec.map σ).opensRange = PrimeSpectrum.basicOpen (Ideal.Quotient.mk (Ideal.ofList s)
    t) :=
    Scheme.Hom.opensRange_localizationAway (R := quotientSpecRing (Ideal.ofList s))
      (Ideal.Quotient.mk (Ideal.ofList s) t)
  exact openSpecSectionsHomology_isLocalized σ (regularClosedResolutionComplex s J)
    (PrimeSpectrum.basicOpen (Ideal.Quotient.mk (Ideal.ofList s) t)) ho
    (Submonoid.powers (Ideal.Quotient.mk (Ideal.ofList s) t)) n
    (quotientLocalizationOpenHomology_isLocalized s hs t J e n)

end ActualCounit
end AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian HomologicalComplex CochainComplex
namespace AlgebraicGeometry.Scheme.Modules
section AffineCounit
variable {R : CommRingCat.{u}} (s : List R)
  (hs : RingTheory.Sequence.IsWeaklyRegular R s)
  {L : (Spec R).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)
  (e : (moduleSpecΓFunctor (R := R)).obj L ≅ ModuleCat.of R R)

local instance : (moduleSpecΓFunctor (R := quotientSpecRing (Ideal.ofList s))).Additive :=
  moduleSpecΓFunctor_additive (quotientSpecRing (Ideal.ofList s))

local instance : PreservesFiniteLimits (tilde.functor (quotientSpecRing (Ideal.ofList s))) :=
  tilde_preservesFiniteLimits (quotientSpecRing (Ideal.ofList s))
local instance : (tilde.functor (quotientSpecRing (Ideal.ofList s))).Additive :=
  CategoryTheory.Functor.additive_of_preserves_binary_products _

include hs e in
private theorem regularClosedResolutionTildeCounit_quasiIso :
    QuasiIso (Complex.tildeGlobalSectionsCounit (quotientSpecRing (Ideal.ofList s)) (.up ℤ)
      (regularClosedResolutionComplex s J)) := by
  let : HasDerivedCategory.{u+1} (ModuleCat.{u} R) := HasDerivedCategory.standard _
  let : HasExt.{u+1} (ModuleCat.{u} R) := hasExt_of_hasDerivedCategory _
  apply Complex.tildeGlobalSectionsCounit_quasiIso_of_isLocalized
  intro x n
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  let : HasDerivedCategory.{u+1} (ModuleCat.{u} (Localization.Away t)) :=
    HasDerivedCategory.standard _
  let : HasExt.{u+1} (ModuleCat.{u} (Localization.Away t)) := hasExt_of_hasDerivedCategory _
  exact quotientResolutionPrincipalSections_isLocalized s hs t J e n

include hs e in
private theorem regularClosedResolutionHomology_quasicoherent (n : ℤ) :
    ((regularClosedResolutionComplex s J).homology n).IsQuasicoherent := by
  let : QuasiIso (Complex.tildeGlobalSectionsCounit (quotientSpecRing (Ideal.ofList s)) (.up ℤ)
    (regularClosedResolutionComplex s J)) := regularClosedResolutionTildeCounit_quasiIso s hs J e
  exact Complex.quasicoherent_homology_of_tildeGlobalSectionsCounit
    (quotientSpecRing (Ideal.ofList s)) (.up ℤ) (regularClosedResolutionComplex s J) n

include hs e in
private theorem regularClosedResolutionHomology_isZero (n : ℤ) (hn : n ≠ (s.length : ℤ)) :
    IsZero ((regularClosedResolutionComplex s J).homology n) := by
  let : HasDerivedCategory.{u+1} (ModuleCat.{u} R) := HasDerivedCategory.standard _
  let : HasExt.{u+1} (ModuleCat.{u} R) := hasExt_of_hasDerivedCategory _
  let : QuasiIso (Complex.tildeGlobalSectionsCounit (quotientSpecRing (Ideal.ofList s)) (.up ℤ)
    (regularClosedResolutionComplex s J)) := regularClosedResolutionTildeCounit_quasiIso s hs J e
  exact ((tilde.functor (quotientSpecRing (Ideal.ofList s))).map_isZero
    (closedΓResolutionRegular_isZero s hs J e n hn)).of_iso
    (Complex.tildeGlobalSectionsHomologyIso (quotientSpecRing (Ideal.ofList s)) (.up ℤ)
      (regularClosedResolutionComplex s J) n).symm

end AffineCounit
end AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian HomologicalComplex CochainComplex
namespace AlgebraicGeometry.Scheme.Modules
section OrderedTopLine
variable {R : CommRingCat.{u}} [HasExt.{w} (ModuleCat.{u} R)]
  (s : List R) (hs : RingTheory.Sequence.IsWeaklyRegular R s)
  {L : (Spec R).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)
  (e : (moduleSpecΓFunctor (R := R)).obj L ≅ ModuleCat.of R R)

private def regularClosedTopSectionsAddEquiv :
    (closedΓResolutionComplex (quotientSpecMap (Ideal.ofList s)) J).homology (s.length : ℤ) ≃+
      (R ⧸ Ideal.ofList s) := by
  letI := Ext.quotientSourceModule (Ideal.ofList s) (ModuleCat.of R R) s.length
  exact (closedΓResolutionExtAddEquiv (quotientSpecMap (Ideal.ofList s)) J s.length).trans
    ((extIsoTransport R (Iso.refl (ModuleCat.of R (R ⧸ Ideal.ofList s))) e
      s.length).toAddEquiv.trans
      (ChainComplex.Koszul.topExtRingQuotientLinearEquiv s hs).symm.toAddEquiv)

private def regularClosedTopSectionsLinearEquiv :
    (closedΓResolutionComplex (quotientSpecMap (Ideal.ofList s)) J).homology (s.length : ℤ) ≃ₗ[R ⧸
      Ideal.ofList s]
      (R ⧸ Ideal.ofList s) := by
  let := Ext.quotientSourceModule (Ideal.ofList s) (ModuleCat.of R R) s.length
  refine {
    __ := regularClosedTopSectionsAddEquiv s hs J e
    map_smul' := ?_ }
  intro b x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective b
  let E := closedΓResolutionExtLinearEquiv (quotientSpecMap (Ideal.ofList s)) J s.length
  let T := extIsoTransport R (Iso.refl (ModuleCat.of R (R ⧸ Ideal.ofList s))) e s.length
  let P := ChainComplex.Koszul.topExtRingQuotientLinearEquiv s hs
  have hR : E (Ideal.Quotient.mk (Ideal.ofList s) r • x) = r • E x := E.map_smul r x
  change P.symm (T (E (Ideal.Quotient.mk (Ideal.ofList s) r • x))) =
    Ideal.Quotient.mk (Ideal.ofList s) r • P.symm (T (E x))
  rw [hR, T.map_smul]
  rw [← Ext.quotientSourceModule_mk_smul (Ideal.ofList s) (ModuleCat.of R R) s.length r]
  exact P.symm.map_smul _ _

private theorem regularClosedTopSectionsLinearEquiv_symm (b : R ⧸ Ideal.ofList s) :
    (regularClosedTopSectionsLinearEquiv s hs J e).symm b =
      (closedΓResolutionExtAddEquiv (quotientSpecMap (Ideal.ofList s)) J s.length).symm
        ((extIsoTransport R (Iso.refl (ModuleCat.of R (R ⧸ Ideal.ofList s))) e s.length).symm
          (ChainComplex.Koszul.topExtRingQuotientLinearEquiv s hs b)) := rfl

private theorem regularClosedTopSectionsLinearEquiv_class (r : R) :
    closedΓResolutionExtAddEquiv (quotientSpecMap (Ideal.ofList s)) J s.length
        ((regularClosedTopSectionsLinearEquiv s hs J e).symm (Ideal.Quotient.mk (Ideal.ofList s)
          r)) =
      (ChainComplex.Koszul.topExtClass s hs (ModuleCat.of R R) r).comp
        (Ext.mk₀ e.inv) (Nat.add_zero s.length) := by
  rw [regularClosedTopSectionsLinearEquiv_symm, AddEquiv.apply_symm_apply,
    ChainComplex.Koszul.topExtRingQuotientLinearEquiv_apply_mk]
  change ((Ext.mk₀ (𝟙 (ModuleCat.of R (R ⧸ Ideal.ofList s)))).comp
      (ChainComplex.Koszul.topExtClass s hs (ModuleCat.of R R) r) (Nat.zero_add s.length)).comp
      (Ext.mk₀ e.inv) (Nat.add_zero s.length) = _
  rw [Ext.mk₀_id_comp]

end OrderedTopLine
end AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian HomologicalComplex CochainComplex
namespace AlgebraicGeometry.Scheme.Modules
section OrderedTopSheaf
variable {R : CommRingCat.{u}} [HasExt.{w} (ModuleCat.{u} R)]
  (s : List R) (hs : RingTheory.Sequence.IsWeaklyRegular R s)
  {L : (Spec R).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)
  (e : (moduleSpecΓFunctor (R := R)).obj L ≅ ModuleCat.of R R)

local instance : PreservesFiniteLimits (tilde.functor (quotientSpecRing (Ideal.ofList s))) :=
  tilde_preservesFiniteLimits (quotientSpecRing (Ideal.ofList s))
local instance : (tilde.functor (quotientSpecRing (Ideal.ofList s))).Additive :=
  CategoryTheory.Functor.additive_of_preserves_binary_products _
local instance : (moduleSpecΓFunctor (R := quotientSpecRing (Ideal.ofList s))).Additive :=
  moduleSpecΓFunctor_additive (quotientSpecRing (Ideal.ofList s))

private def regularClosedResolutionTopHomologyIso :
    (regularClosedResolutionComplex s J).homology (s.length : ℤ) ≅
      SheafOfModules.unit (Spec (quotientSpecRing (Ideal.ofList s))).ringCatSheaf := by
  let : QuasiIso (Complex.tildeGlobalSectionsCounit (quotientSpecRing (Ideal.ofList s)) (.up ℤ)
    (regularClosedResolutionComplex s J)) := regularClosedResolutionTildeCounit_quasiIso s hs J e
  exact (Complex.tildeGlobalSectionsHomologyIso (quotientSpecRing (Ideal.ofList s)) (.up ℤ)
      (regularClosedResolutionComplex s J) (s.length : ℤ)).symm ≪≫
    (tilde.functor (quotientSpecRing (Ideal.ofList s))).mapIso
      (regularClosedTopSectionsLinearEquiv s hs J e).toModuleIso ≪≫
    tildeSelf (R := quotientSpecRing (Ideal.ofList s))

private theorem regularClosedResolutionTopHomologyIso_hom :
    let : QuasiIso (Complex.tildeGlobalSectionsCounit (quotientSpecRing (Ideal.ofList s)) (.up ℤ)
      (regularClosedResolutionComplex s J)) := regularClosedResolutionTildeCounit_quasiIso s hs J e
    (regularClosedResolutionTopHomologyIso s hs J e).hom =
      (Complex.tildeGlobalSectionsHomologyIso (quotientSpecRing (Ideal.ofList s)) (.up ℤ)
        (regularClosedResolutionComplex s J) (s.length : ℤ)).inv ≫
      (tilde.functor (quotientSpecRing (Ideal.ofList s))).map
        (regularClosedTopSectionsLinearEquiv s hs J e).toModuleIso.hom ≫
      (tildeSelf (R := quotientSpecRing (Ideal.ofList s))).hom := rfl

end OrderedTopSheaf
end AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian HomologicalComplex CochainComplex

public section
namespace AlgebraicGeometry.Scheme.Modules
section PublicModels
variable {R : CommRingCat.{u}}

/-- The actual native closed right adjoint applied to the supplied original resolution. -/
abbrev closedImmersionRightAdjointRegularListResolutionComplex (s : List R)
    {L : (Spec R).Modules} (J : InjectiveResolution L) :
    CochainComplex (Spec (.of (R ⧸ Ideal.ofList s))).Modules ℤ :=
  ((closedImmersionRightAdjoint (Spec.map (CommRingCat.ofHom
    (Ideal.Quotient.mk (Ideal.ofList s))))).mapHomologicalComplex (.up ℤ)).obj J.cochainComplex

variable (s : List R) {L : (Spec R).Modules} [L.IsQuasicoherent]

local instance : (moduleSpecΓFunctor (R := CommRingCat.of (R ⧸ Ideal.ofList s))).Additive :=
  moduleSpecΓFunctor_additive (CommRingCat.of (R ⧸ Ideal.ofList s))

/-- The original affine right-adjoint comparison and native extension-by-zero comparison. -/
def closedImmersionRightAdjointRegularListResolutionSectionsIso (J : InjectiveResolution L) :
    ((moduleSpecΓFunctor (R := .of (R ⧸ Ideal.ofList s))).mapHomologicalComplex (.up ℤ)).obj
        (closedImmersionRightAdjointRegularListResolutionComplex s J) ≅
      ((ModuleCat.coextendScalars (Ideal.Quotient.mk (Ideal.ofList s))).mapHomologicalComplex (.up
        ℤ)).obj
        (AffineDerived.globalSectionsInjectiveResolution J).cochainComplex :=
  closedΓResolutionIso (quotientSpecMap (Ideal.ofList s)) J

variable [HasExt.{w} (ModuleCat.{u} R)]

/-- Sections of the actual resolution model compute native Ext through unchanged cocycles. -/
def closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv
    (J : InjectiveResolution L) (n : ℕ) :
    (((moduleSpecΓFunctor (R := .of (R ⧸ Ideal.ofList s))).mapHomologicalComplex (.up ℤ)).obj
      (closedImmersionRightAdjointRegularListResolutionComplex s J)).homology (n : ℤ) ≃+
      Ext.{w} (ModuleCat.of R (R ⧸ Ideal.ofList s)) (moduleSpecΓFunctor.obj L) n :=
  closedΓResolutionExtAddEquiv (quotientSpecMap (Ideal.ofList s)) J n

/-- The native quotient line, normalized by the original ordered Koszul top class. -/
def closedImmersionRightAdjointRegularListResolutionTopSectionsLinearEquiv
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (J : InjectiveResolution L)
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of R R) :
    (((moduleSpecΓFunctor (R := .of (R ⧸ Ideal.ofList s))).mapHomologicalComplex (.up ℤ)).obj
      (closedImmersionRightAdjointRegularListResolutionComplex s J)).homology (s.length : ℤ) ≃ₗ[R
        ⧸ Ideal.ofList s]
      (R ⧸ Ideal.ofList s) :=
  regularClosedTopSectionsLinearEquiv s hs J e

/-- Original inverse counit homology, exact tilde of the ordered line, and the original unit
  sheaf. -/
def closedImmersionRightAdjointRegularListResolutionTopHomologyIso
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (J : InjectiveResolution L)
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of R R) :
    (closedImmersionRightAdjointRegularListResolutionComplex s J).homology (s.length : ℤ) ≅
      SheafOfModules.unit (Spec (.of (R ⧸ Ideal.ofList s))).ringCatSheaf :=
  regularClosedResolutionTopHomologyIso s hs J e

end PublicModels
section PrivatePublicExtFormula
variable {R : CommRingCat.{u}} (s : List R) {L : (Spec R).Modules} [L.IsQuasicoherent]
  [HasExt.{w} (ModuleCat.{u} R)]
local instance : (moduleSpecΓFunctor (R := CommRingCat.of (R ⧸ Ideal.ofList s))).Additive :=
  moduleSpecΓFunctor_additive (CommRingCat.of (R ⧸ Ideal.ofList s))
private theorem closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv_apply_aux
    (J : InjectiveResolution L) (n : ℕ)
    (x : (((moduleSpecΓFunctor (R := .of (R ⧸ Ideal.ofList s))).mapHomologicalComplex (.up ℤ)).obj
      (closedImmersionRightAdjointRegularListResolutionComplex s J)).homology (n : ℤ)) :
    closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s J n x =
      ModuleCat.coextendScalarsResolutionExtAddEquiv (Ideal.Quotient.mk (Ideal.ofList s))
        (AffineDerived.globalSectionsInjectiveResolution J) n
        (homologyMap (closedImmersionRightAdjointRegularListResolutionSectionsIso s J).hom (n : ℤ)
          x) := rfl
private theorem closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv_eq_affine_aux
    (J : InjectiveResolution L) (n : ℕ) :
    closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s J n =
      affineClosedRightAdjointResolutionExtAddEquiv
        (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s))) J n := rfl
end PrivatePublicExtFormula
end AlgebraicGeometry.Scheme.Modules
@[expose] public section
namespace AlgebraicGeometry.Scheme.Modules
section PublicModelLaws
variable {R : CommRingCat.{u}}

variable (s : List R) {L : (Spec R).Modules} [L.IsQuasicoherent]

local instance : (moduleSpecΓFunctor (R := CommRingCat.of (R ⧸ Ideal.ofList s))).Additive :=
  moduleSpecΓFunctor_additive (CommRingCat.of (R ⧸ Ideal.ofList s))

/-- The original affine comparison and native retained-degree extension map are unchanged. -/
theorem closedImmersionRightAdjointRegularListResolutionSectionsIso_hom_f
    (J : InjectiveResolution L) (n : ℕ) :
    (closedImmersionRightAdjointRegularListResolutionSectionsIso s J).hom.f (n : ℤ) ≫
        (ModuleCat.coextendScalars (Ideal.Quotient.mk (Ideal.ofList s))).map
          ((AffineDerived.globalSectionsInjectiveResolution J).cochainComplexXIso n n rfl).hom =
      (closedImmersionRightAdjointAffineIso (CommRingCat.ofHom
        (Ideal.Quotient.mk (Ideal.ofList s)))).hom.app (J.cochainComplex.X (n : ℤ)) ≫
        (ModuleCat.coextendScalars (Ideal.Quotient.mk (Ideal.ofList s))).map
          (moduleSpecΓFunctor.map (J.cochainComplexXIso n n rfl).hom) :=
  closedΓResolutionIso_hom_f (quotientSpecMap (Ideal.ofList s)) J n

/-- The same native tilde-global-sections counit is a quasi-isomorphism on the actual Ri! model. -/
theorem closedImmersionRightAdjointRegularListResolutionTildeCounit_quasiIso
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (J : InjectiveResolution L)
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of R R) :
    QuasiIso (Complex.tildeGlobalSectionsCounit (.of (R ⧸ Ideal.ofList s)) (.up ℤ)
      (closedImmersionRightAdjointRegularListResolutionComplex s J)) :=
  regularClosedResolutionTildeCounit_quasiIso s hs J e

/-- Every original homology sheaf of the supplied actual model is quasicoherent. -/
theorem closedImmersionRightAdjointRegularListResolutionHomology_quasicoherent
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (J : InjectiveResolution L)
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of R R) (n : ℤ) :
    ((closedImmersionRightAdjointRegularListResolutionComplex s J).homology n).IsQuasicoherent :=
  regularClosedResolutionHomology_quasicoherent s hs J e n

/-- Only the list-length homology survives for the framed ring coefficient. -/
theorem closedImmersionRightAdjointRegularListResolutionHomology_isZero
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (J : InjectiveResolution L)
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of R R) (n : ℤ) (hn : n ≠ (s.length : ℤ)) :
    IsZero ((closedImmersionRightAdjointRegularListResolutionComplex s J).homology n) :=
  regularClosedResolutionHomology_isZero s hs J e n hn

variable [HasExt.{w} (ModuleCat.{u} R)]

/-- The specialized comparison is the same original canonical affine Ext comparison. -/
theorem closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv_eq_affine
    (J : InjectiveResolution L) (n : ℕ) :
    closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s J n =
      affineClosedRightAdjointResolutionExtAddEquiv
        (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.ofList s))) J n :=
  closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv_eq_affine_aux s J n

/-- The Ext comparison has the original cochain isomorphism and native coinduction forward
  factors. -/
theorem closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv_apply
    (J : InjectiveResolution L) (n : ℕ)
    (x : (((moduleSpecΓFunctor (R := .of (R ⧸ Ideal.ofList s))).mapHomologicalComplex (.up ℤ)).obj
      (closedImmersionRightAdjointRegularListResolutionComplex s J)).homology (n : ℤ)) :
    closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s J n x =
      ModuleCat.coextendScalarsResolutionExtAddEquiv (Ideal.Quotient.mk (Ideal.ofList s))
        (AffineDerived.globalSectionsInjectiveResolution J) n
        (homologyMap (closedImmersionRightAdjointRegularListResolutionSectionsIso s J).hom (n : ℤ)
          x) :=
  closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv_apply_aux s J n x

/-- Ring representatives act by the original R-action, with no derived-functor linearity instance.
-/
theorem closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv_smul
    (J : InjectiveResolution L) (n : ℕ) (r : R)
    (x : (((moduleSpecΓFunctor (R := .of (R ⧸ Ideal.ofList s))).mapHomologicalComplex (.up ℤ)).obj
      (closedImmersionRightAdjointRegularListResolutionComplex s J)).homology (n : ℤ)) :
    closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s J n
        (Ideal.Quotient.mk (Ideal.ofList s) r • x) =
      r • closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s J n x :=
  (closedΓResolutionExtLinearEquiv (quotientSpecMap (Ideal.ofList s)) J n).map_smul r x

/-- A literal quotient representative is the original ordered top class with the original frame
  inverse. -/
theorem closedImmersionRightAdjointRegularListResolutionTopSectionsLinearEquiv_class
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (J : InjectiveResolution L)
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of R R) (r : R) :
    closedImmersionRightAdjointRegularListResolutionSectionsExtAddEquiv s J s.length
        ((closedImmersionRightAdjointRegularListResolutionTopSectionsLinearEquiv s hs J e).symm
          (Ideal.Quotient.mk (Ideal.ofList s) r)) =
      (ChainComplex.Koszul.topExtClass s hs (ModuleCat.of R R) r).comp
        (Ext.mk₀ e.inv) (Nat.add_zero s.length) :=
  regularClosedTopSectionsLinearEquiv_class s hs J e r

/-- The top sheaf frame retains the inverse actual counit, exact tilde, and original tildeSelf. -/
theorem closedImmersionRightAdjointRegularListResolutionTopHomologyIso_hom
    (hs : RingTheory.Sequence.IsWeaklyRegular R s) (J : InjectiveResolution L)
    (e : moduleSpecΓFunctor.obj L ≅ ModuleCat.of R R) :
    let : QuasiIso (Complex.tildeGlobalSectionsCounit (.of (R ⧸ Ideal.ofList s)) (.up ℤ)
      (closedImmersionRightAdjointRegularListResolutionComplex s J)) :=
        closedImmersionRightAdjointRegularListResolutionTildeCounit_quasiIso s hs J e
    (closedImmersionRightAdjointRegularListResolutionTopHomologyIso s hs J e).hom =
      (Complex.tildeGlobalSectionsHomologyIso (.of (R ⧸ Ideal.ofList s)) (.up ℤ)
        (closedImmersionRightAdjointRegularListResolutionComplex s J) (s.length : ℤ)).inv ≫
        (tilde.functor (.of (R ⧸ Ideal.ofList s))).map
          (closedImmersionRightAdjointRegularListResolutionTopSectionsLinearEquiv s hs J
            e).toModuleIso.hom ≫
        (tildeSelf (R := .of (R ⧸ Ideal.ofList s))).hom :=
  regularClosedResolutionTopHomologyIso_hom s hs J e

end PublicModelLaws
end AlgebraicGeometry.Scheme.Modules
