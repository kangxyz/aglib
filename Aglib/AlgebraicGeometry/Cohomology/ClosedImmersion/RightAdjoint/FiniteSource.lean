/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.Cohomology.ClosedImmersion.RightAdjoint.RegularList.Sheaf.Localization
public import Aglib.Algebra.Category.ModuleCat.Ext.Localization
public import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
public import Aglib.AlgebraicGeometry.Modules.FinitePresentation.Noetherian

/-!
# The original closed-adjoint resolution for a finite quotient source

For an arbitrary ideal of a Noetherian affine ambient ring, the original
closed-adjoint image of a supplied injective resolution has a quasi-isomorphic
tilde-global-sections counit. Its homology is quasicoherent in every degree.
When the quasicoherent coefficient has finite global sections, its homology is
also finite and finitely presented as a sheaf.

The proof retains the original principal-open restriction, quotient-source
isomorphism, coefficient comparison and exact-functor Ext map. No regular
sequence, coefficient frame, Gorenstein assumption, Cohen--Macaulay assumption,
or quasicoherence of the individual injective terms is required. The current
consumer is the affine part of chosen-embedding surface duality.
-/

noncomputable section

universe u w z u1 v1 w1 r1

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open scoped TensorProduct ChangeOfRings

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

private abbrev closedΓResolutionIso (q : R ⟶ A) [IsClosedImmersion (Spec.map q)]
    {L : (Spec R).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L) :=
  affineClosedRightAdjointResolutionSectionsIso q J
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

/-- Build the original scalar comparison at variable rings, so its homology
carrier and its linear map use the same ring structure before localization. -/
private def closedΓResolutionExtLinearEquivOver
    {B S A T : CommRingCat.{u}} [Algebra B A] [HasExt.{z} (ModuleCat.{u} A)]
    (q : B ⟶ S) (ψ : S ⟶ T) (q' : A ⟶ T) [IsClosedImmersion (Spec.map q')]
    (hcomm : ∀ b : B, q'.hom (algebraMap B A b) = ψ.hom (q.hom b))
    {N : (Spec A).Modules} [N.IsQuasicoherent] (J : InjectiveResolution N) (n : ℕ) :
    (ModuleCat.restrictScalars q.hom).obj
      ((ModuleCat.restrictScalars ψ.hom).obj
        ((closedΓResolutionComplex q' J).homology (n : ℤ))) ≃ₗ[B]
      Ext.{z} ((ModuleCat.restrictScalars q'.hom).obj (ModuleCat.of T T))
        (moduleSpecΓFunctor.obj N) n where
  __ := closedΓResolutionExtAddEquiv q' J n
  map_smul' b x := by
    change (closedΓResolutionComplex q' J).homology (n : ℤ) at x
    let IR := AffineDerived.globalSectionsInjectiveResolution J
    let E := ModuleCat.coextendScalarsResolutionExtAddEquiv q'.hom IR n
    let f : (closedΓResolutionComplex q' J).homology (n : ℤ) →ₗ[T]
        ((((ModuleCat.coextendScalars q'.hom).mapHomologicalComplex (.up ℤ)).obj
          IR.cochainComplex).homology (n : ℤ)) :=
      ((homologyFunctor (ModuleCat.{u} T) (.up ℤ) (n : ℤ)).mapIso
        (closedΓResolutionIso q' J)).hom.hom
    change E (f (ψ.hom (q.hom b) • x)) = b • E (f x)
    have hm : (ModuleCat.restrictScalars q'.hom).map
        (ModuleCat.ofHom (X := ModuleCat.of T T) (Y := ModuleCat.of T T)
          (LinearMap.mulRight T (q'.hom (algebraMap B A b)))) =
        b • 𝟙 ((ModuleCat.restrictScalars q'.hom).obj (ModuleCat.of T T)) := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro y
      change (show T from y) * q'.hom (algebraMap B A b) =
        q'.hom (algebraMap B A b) * (show T from y)
      exact mul_comm _ _
    calc
      E (f (ψ.hom (q.hom b) • x)) = E (f (q'.hom (algebraMap B A b) • x)) :=
        congrArg (fun a : T => E (f (a • x))) (hcomm b).symm
      _ = E (q'.hom (algebraMap B A b) • f x) :=
        congrArg E (f.map_smul (q'.hom (algebraMap B A b)) x)
      _ = (Ext.mk₀ ((ModuleCat.restrictScalars q'.hom).map
          (ModuleCat.ofHom (X := ModuleCat.of T T) (Y := ModuleCat.of T T)
            (LinearMap.mulRight T (q'.hom (algebraMap B A b)))))).comp
          (E (f x)) (zero_add n) :=
        ModuleCat.coextendScalarsResolutionExtAddEquiv_smul q'.hom IR n
          (q'.hom (algebraMap B A b)) (f x)
      _ = b • E (f x) := by
        rw [hm]
        simp only [Ext.mk₀_smul, Ext.smul_comp, Ext.mk₀_id_comp]

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
          ((restrictFunctor (Spec.map (ambientAwayUnit t))).obj L)) n :=
  closedΓResolutionExtLinearEquivOver (quotientSpecMap I) (quotientAwayUnit I t)
    (localizedQuotientSpecMap I t)
    (fun r => ConcreteCategory.congr_hom
      (CommRingCat.localizationAway_map_comm (quotientSpecMap I) t) r)
    (openRestrictedInjectiveResolution (ambientAwayUnit t) J) n

end LocalLinear
end AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian HomologicalComplex CochainComplex
open scoped ModuleCat.Algebra
namespace AlgebraicGeometry.Scheme.Modules
section FiniteLocalization
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

private theorem quotientLocalizationExt_isLocalized [IsNoetherianRing R]
    (N : (Spec R).Modules) [N.IsQuasicoherent] (n : ℕ) :
    IsLocalizedModule (Submonoid.powers t)
      (quotientLocalizationExtLinearMap I t N n) := by
  let b := (ModuleCat.extendScalars (ambientAwayUnit t).hom).mapExtLinearMap R
    (ModuleCat.of R (R ⧸ I)) (moduleSpecΓFunctor.obj N) n
  let : IsLocalizedModule (Submonoid.powers t) b :=
    ModuleCat.extScalarExtension_isLocalized_of_finite
      (A := Localization.Away t) (Submonoid.powers t)
      (ModuleCat.of R (R ⧸ I)) (moduleSpecΓFunctor.obj N) n
  exact IsLocalizedModule.of_linearEquiv (Submonoid.powers t) b
    (quotientLocalizationExtTransport I t N n)

end FiniteLocalization
end AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian HomologicalComplex CochainComplex
open scoped ModuleCat.Algebra
namespace AlgebraicGeometry.Scheme.Modules
section GeometricLocalization
variable {R : CommRingCat.{u}} [IsNoetherianRing R] (I : Ideal R) (t : R)
  {L : (Spec R).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)

local instance : IsClosedImmersion
    (Spec.map (localizedQuotientSpecMap I t)) :=
  Scheme.isClosedImmersion_specMap_localizationAway (quotientSpecMap I) t
local instance : (moduleSpecΓFunctor (R := quotientAwaySpecRing I t)).Additive :=
  moduleSpecΓFunctor_additive (quotientAwaySpecRing I t)
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

private theorem quotientLocalizationGeoHomology_nonneg_isLocalized_R (n : ℕ) :
    IsLocalizedModule (Submonoid.powers t)
      (((ModuleCat.restrictScalars (quotientSpecMap I).hom).map
        (quotientLocalizationGeoHomology I t J (n : ℤ))).hom) := by
  let b := quotientLocalizationExtLinearMap I t L n
  let E := closedΓResolutionExtLinearEquiv (quotientSpecMap I) J n
  let E' := quotientLocalΓExtLinearEquiv I t J n
  let f := (ModuleCat.restrictScalars (quotientSpecMap I).hom).map
    (quotientLocalizationGeoHomology I t J (n : ℤ))
  have he : f.hom = E'.symm.toLinearMap.comp (b.comp E.toLinearMap) := by
    apply LinearMap.ext
    intro x
    apply E'.injective
    change E' (f x) = E' (E'.symm (b (E x)))
    rw [E'.apply_symm_apply]
    exact quotientLocalizationGeoHomology_ext I t J n x
  let : IsLocalizedModule (Submonoid.powers t) b :=
    quotientLocalizationExt_isLocalized I t L n
  let : IsLocalizedModule (Submonoid.powers t) (b.comp E.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right (Submonoid.powers t) b E
  have h : IsLocalizedModule (Submonoid.powers t)
      (E'.symm.toLinearMap.comp (b.comp E.toLinearMap)) :=
    IsLocalizedModule.of_linearEquiv (Submonoid.powers t) (b.comp E.toLinearMap) E'.symm
  change IsLocalizedModule (Submonoid.powers t) f.hom
  rw [he]
  exact h

private theorem quotientLocalizationGeoHomology_nonneg_isLocalized (n : ℕ) :
    IsLocalizedModule (Submonoid.powers (Ideal.Quotient.mk I t))
      (quotientLocalizationGeoHomology I t J (n : ℤ)).hom := by
  let f := (quotientLocalizationGeoHomology I t J (n : ℤ)).hom
  let : IsLocalizedModule (Submonoid.powers t) (f.restrictScalars R) :=
    quotientLocalizationGeoHomology_nonneg_isLocalized_R I t J n
  have h := IsLocalizedModule.of_restrictScalars (A := R ⧸ I)
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
    change IsIso (N.presheaf.mapIso (eqToIso he).op).hom
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
    change IsIso (N.presheaf.mapIso (eqToIso he.symm).op).hom
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

namespace AlgebraicGeometry.Scheme.Modules

@[expose] public section QuotientResolutionComplex

/-- The original closed-adjoint image of the supplied ambient injective resolution. -/
public def closedImmersionRightAdjointQuotientResolutionComplex
    {R : CommRingCat.{u}} (I : Ideal R) {L : (Spec R).Modules}
    (J : InjectiveResolution L) : CochainComplex (Spec (.of (R ⧸ I))).Modules ℤ :=
  ((closedImmersionRightAdjoint
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).mapHomologicalComplex (.up ℤ)).obj
      J.cochainComplex

end QuotientResolutionComplex

section NegativeDegrees
variable {R A : CommRingCat.{u}} (φ : R ⟶ A) [IsClosedImmersion (Spec.map φ)]
  {L : (Spec R).Modules} (J : InjectiveResolution L)

local instance : (moduleSpecΓFunctor (R := A)).Additive := moduleSpecΓFunctor_additive A

private theorem closedΓResolution_isZero_of_neg (n : ℤ) (hn : n < 0) :
    IsZero ((closedΓResolutionComplex φ J).homology n) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _
    ((moduleSpecΓFunctor (R := A)).map_isZero
      ((closedImmersionRightAdjoint (Spec.map φ)).map_isZero
        (J.cochainComplex.isZero_of_isStrictlyGE 0 n hn)))

end NegativeDegrees

section ActualCounit
variable {R : CommRingCat.{u}} [IsNoetherianRing R] (I : Ideal R) (t : R)
  {L : (Spec R).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)

local instance : IsClosedImmersion (Spec.map (localizedQuotientSpecMap I t)) :=
  Scheme.isClosedImmersion_specMap_localizationAway (quotientSpecMap I) t
local instance : (moduleSpecΓFunctor (R := quotientSpecRing I)).Additive :=
  moduleSpecΓFunctor_additive (quotientSpecRing I)
local instance : (moduleSpecΓFunctor (R := quotientAwaySpecRing I t)).Additive :=
  moduleSpecΓFunctor_additive (quotientAwaySpecRing I t)

variable [HasExt.{w} (ModuleCat.{u} R)]
  [HasExt.{z} (ModuleCat.{u} (ambientAwayRing t))]

private theorem quotientLocalizationGeoHomology_isLocalized (n : ℤ) :
    IsLocalizedModule (Submonoid.powers (Ideal.Quotient.mk I t))
      (quotientLocalizationGeoHomology I t J n).hom := by
  by_cases hneg : n < 0
  · let : Subsingleton ((closedΓResolutionComplex (quotientSpecMap I) J).homology n) :=
      ModuleCat.subsingleton_of_isZero
        (closedΓResolution_isZero_of_neg (quotientSpecMap I) J n hneg)
    let : Subsingleton ((ModuleCat.restrictScalars (quotientAwayUnit I t).hom).obj
        ((quotientLocalΓComplex I t J).homology n)) :=
      ModuleCat.subsingleton_of_isZero
        ((ModuleCat.restrictScalars (quotientAwayUnit I t).hom).map_isZero
          (closedΓResolution_isZero_of_neg (localizedQuotientSpecMap I t)
            (openRestrictedInjectiveResolution (ambientAwayUnit t) J) n hneg))
    refine ⟨?_, ?_, ?_⟩
    · intro a
      apply (Module.End.isUnit_iff _).mpr
      exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
    · intro y
      exact ⟨⟨0, 1⟩, Subsingleton.elim _ _⟩
    · intro x y h
      exact ⟨1, Subsingleton.elim _ _⟩
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hneg)
    exact quotientLocalizationGeoHomology_nonneg_isLocalized I t J q

private theorem quotientLocalizationOpenHomology_isLocalized (n : ℤ) :
    IsLocalizedModule (Submonoid.powers (Ideal.Quotient.mk I t))
      (homologyMap (openSpecRestrictionComplex (quotientAwayUnit I t)
        (closedImmersionRightAdjointQuotientResolutionComplex I J)) n).hom := by
  let K := ((closedImmersionRightAdjoint (Spec.map (quotientSpecMap I))).mapHomologicalComplex
    (.up ℤ)).obj J.cochainComplex
  let β := openSpecRestrictionComplex (quotientAwayUnit I t) K
  let a := quotientAfterOpenSectionsIso I t J
  have hfa : β ≫ a.hom = quotientLocalizationGeoComplex I t J :=
    (quotientLocalizationGeoComplex_factor I t J).symm
  change IsLocalizedModule (Submonoid.powers (Ideal.Quotient.mk I t))
    (homologyMap β n).hom
  apply localized_homologyMap_of_postIso
    (Submonoid.powers (Ideal.Quotient.mk I t)) β a n
  rw [hfa]
  have he : quotientLocalizationGeoHomology I t J n =
      homologyMap (quotientLocalizationGeoComplex I t J) n ≫
        (((quotientLocalΓComplex I t J).sc n).mapHomologyIso
          (ModuleCat.restrictScalars (quotientAwayUnit I t).hom)).hom := by
    exact closedImmersionQuotientLocalizationHomologyMap_eq I t J n
  have h := quotientLocalizationGeoHomology_isLocalized I t J n
  rw [he] at h
  exact localized_homologyMap_of_restrictComparison (quotientAwayUnit I t).hom
    (Submonoid.powers (Ideal.Quotient.mk I t))
    (closedΓResolutionComplex (quotientSpecMap I) J)
    (quotientLocalΓComplex I t J)
    (quotientLocalizationGeoComplex I t J) n h

private theorem quotientResolutionPrincipalSections_isLocalized (n : ℤ) :
    specSectionsHomologyLocalizes (closedImmersionRightAdjointQuotientResolutionComplex I J)
      (PrimeSpectrum.basicOpen (Ideal.Quotient.mk I t))
      (Submonoid.powers (Ideal.Quotient.mk I t)) n := by
  let σ := quotientAwayUnit I t
  have ho : (Spec.map σ).opensRange = PrimeSpectrum.basicOpen (Ideal.Quotient.mk I
    t) :=
    Scheme.Hom.opensRange_localizationAway (R := quotientSpecRing I)
      (Ideal.Quotient.mk I t)
  exact openSpecSectionsHomology_isLocalized σ
    (closedImmersionRightAdjointQuotientResolutionComplex I J)
    (PrimeSpectrum.basicOpen (Ideal.Quotient.mk I t)) ho
    (Submonoid.powers (Ideal.Quotient.mk I t)) n
    (quotientLocalizationOpenHomology_isLocalized I t J n)


end ActualCounit
end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
section FiniteSourceCounit
variable {R : CommRingCat.{u}} [IsNoetherianRing R] (I : Ideal R)
  {L : (Spec R).Modules} [L.IsQuasicoherent] (J : InjectiveResolution L)

public local instance : (moduleSpecΓFunctor (R := CommRingCat.of (R ⧸ I))).Additive :=
  moduleSpecΓFunctor_additive (.of (R ⧸ I))
public local instance : PreservesFiniteLimits (tilde.functor (.of (R ⧸ I))) :=
  tilde_preservesFiniteLimits (.of (R ⧸ I))
public local instance : (tilde.functor (.of (R ⧸ I))).PreservesHomology :=
  tilde_preservesHomology (.of (R ⧸ I))
public local instance : (tilde.functor (.of (R ⧸ I))).Additive :=
  CategoryTheory.Functor.additive_of_preserves_binary_products _

/-- The original quotient-localization homology map localizes in every degree.
The nonnegative calculation uses the original exact-functor Ext map. -/
public theorem closedImmersionQuotientLocalizationHomologyMap_isLocalized (t : R) (n : ℤ) :
    IsLocalizedModule (Submonoid.powers (Ideal.Quotient.mk I t))
      (closedImmersionQuotientLocalizationHomologyMap I t J n).hom := by
  let : HasExt.{u+1} (ModuleCat.{u} R) := HasExt.standard _
  let : HasExt.{u+1} (ModuleCat.{u} (Localization.Away t)) := HasExt.standard _
  exact quotientLocalizationGeoHomology_isLocalized I t J n

/-- Actual restriction of the original closed-adjoint resolution to a principal
open localizes homology; arbitrary quotient elements are allowed. -/
public theorem closedImmersionRightAdjointQuotientResolutionPrincipalSections_isLocalized
    (b : R ⧸ I) (n : ℤ) :
    IsLocalizedModule (Submonoid.powers b)
      (homologyMap (Complex.specSectionsComplexRestriction (.of (R ⧸ I)) (.up ℤ)
        (PrimeSpectrum.basicOpen b)
        (closedImmersionRightAdjointQuotientResolutionComplex I J)) n).hom := by
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective b
  let : HasExt.{u+1} (ModuleCat.{u} R) := HasExt.standard _
  let : HasExt.{u+1} (ModuleCat.{u} (Localization.Away t)) := HasExt.standard _
  exact quotientResolutionPrincipalSections_isLocalized I t J n

/-- The actual tilde-global-sections counit of the original closed-adjoint
resolution is a quasi-isomorphism for every ideal of a Noetherian ring. -/
public theorem closedImmersionRightAdjointQuotientResolutionTildeCounit_quasiIso :
    QuasiIso (Complex.tildeGlobalSectionsCounit (.of (R ⧸ I)) (.up ℤ)
      (closedImmersionRightAdjointQuotientResolutionComplex I J)) := by
  apply Complex.tildeGlobalSectionsCounit_quasiIso_of_isLocalized
  exact closedImmersionRightAdjointQuotientResolutionPrincipalSections_isLocalized I J

/-- Exact native tilde and the original counit compute the actual homology sheaf. -/
@[expose] public def closedImmersionRightAdjointQuotientResolutionHomologyIso (n : ℤ) :
    tilde ((((moduleSpecΓFunctor (R := .of (R ⧸ I))).mapHomologicalComplex (.up ℤ)).obj
      (closedImmersionRightAdjointQuotientResolutionComplex I J)).homology n) ≅
      (closedImmersionRightAdjointQuotientResolutionComplex I J).homology n := by
  let : QuasiIso (Complex.tildeGlobalSectionsCounit (.of (R ⧸ I)) (.up ℤ)
      (closedImmersionRightAdjointQuotientResolutionComplex I J)) :=
    closedImmersionRightAdjointQuotientResolutionTildeCounit_quasiIso I J
  exact Complex.tildeGlobalSectionsHomologyIso (.of (R ⧸ I)) (.up ℤ)
    (closedImmersionRightAdjointQuotientResolutionComplex I J) n

/-- The affine homology comparison retains the actual counit homology map. -/
public theorem closedImmersionRightAdjointQuotientResolutionHomologyIso_hom (n : ℤ) :
    (closedImmersionRightAdjointQuotientResolutionHomologyIso I J n).hom =
      (((((moduleSpecΓFunctor (R := .of (R ⧸ I))).mapHomologicalComplex (.up ℤ)).obj
        (closedImmersionRightAdjointQuotientResolutionComplex I J)).sc n).mapHomologyIso
          (tilde.functor (.of (R ⧸ I)))).inv ≫
        homologyMap (Complex.tildeGlobalSectionsCounit (.of (R ⧸ I)) (.up ℤ)
          (closedImmersionRightAdjointQuotientResolutionComplex I J)) n := rfl

/-- Homology of the original closed-adjoint resolution is quasicoherent in all degrees. -/
public theorem closedImmersionRightAdjointQuotientResolutionHomology_quasicoherent (n : ℤ) :
    ((closedImmersionRightAdjointQuotientResolutionComplex I J).homology n).IsQuasicoherent := by
  let : QuasiIso (Complex.tildeGlobalSectionsCounit (.of (R ⧸ I)) (.up ℤ)
      (closedImmersionRightAdjointQuotientResolutionComplex I J)) :=
    closedImmersionRightAdjointQuotientResolutionTildeCounit_quasiIso I J
  exact Complex.quasicoherent_homology_of_tildeGlobalSectionsCounit
    (.of (R ⧸ I)) (.up ℤ) (closedImmersionRightAdjointQuotientResolutionComplex I J) n

end FiniteSourceCounit

/-- Negative homology vanishes by the nonnegative injective resolution and
additivity of the actual closed right adjoint. No finiteness is required. -/
public theorem closedImmersionRightAdjointQuotientResolutionHomology_isZero_of_neg
    {R : CommRingCat.{u}} (I : Ideal R) {L : (Spec R).Modules}
    (J : InjectiveResolution L) (n : ℤ) (hn : n < 0) :
    IsZero ((closedImmersionRightAdjointQuotientResolutionComplex I J).homology n) :=
  ShortComplex.isZero_homology_of_isZero_X₂ _
    ((closedImmersionRightAdjoint (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)))).map_isZero
      (J.cochainComplex.isZero_of_isStrictlyGE 0 n hn))

section FiniteCoefficient
variable {R : CommRingCat.{u}} [IsNoetherianRing R] (I : Ideal R)
  {L : (Spec R).Modules} [L.IsQuasicoherent]
  [Module.Finite R (moduleSpecΓFunctor.obj L)] (J : InjectiveResolution L)

public local instance : (moduleSpecΓFunctor (R := CommRingCat.of (R ⧸ I))).Additive :=
  moduleSpecΓFunctor_additive (.of (R ⧸ I))

/-- Finite coefficient sections give finite homology of the actual section
complex. Nonnegative degrees use native finite Ext, with its original R-action. -/
public theorem closedImmersionRightAdjointQuotientResolutionSectionsHomology_finite (n : ℤ) :
    Module.Finite (R ⧸ I)
      ((((moduleSpecΓFunctor (R := .of (R ⧸ I))).mapHomologicalComplex (.up ℤ)).obj
        (closedImmersionRightAdjointQuotientResolutionComplex I J)).homology n) := by
  by_cases hneg : n < 0
  · change Module.Finite (R ⧸ I)
      ((closedΓResolutionComplex (quotientSpecMap I) J).homology n)
    let : Subsingleton ((closedΓResolutionComplex (quotientSpecMap I) J).homology n) :=
      ModuleCat.subsingleton_of_isZero
        (closedΓResolution_isZero_of_neg (quotientSpecMap I) J n hneg)
    exact Module.Finite.of_surjective (0 : (R ⧸ I) →ₗ[R ⧸ I] _)
      (fun x => ⟨0, Subsingleton.elim _ _⟩)
  · obtain ⟨q, rfl⟩ := Int.eq_ofNat_of_zero_le (le_of_not_gt hneg)
    let M := (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
      ((closedΓResolutionComplex (quotientSpecMap I) J).homology (q : ℤ))
    let P := (ModuleCat.restrictScalars (quotientSpecMap I).hom).obj
      (ModuleCat.of (quotientSpecRing I) (quotientSpecRing I))
    let : Module.Finite R P := by
      change Module.Finite R (R ⧸ I)
      infer_instance
    let E := affineClosedRightAdjointResolutionExtLinearEquiv.{u, u} (quotientSpecMap I) J q
    let : Module.Finite R M := Module.Finite.equiv E.symm
    let : IsScalarTower R (R ⧸ I) M := ⟨fun r a m => by
      change (r • a) • m = (Ideal.Quotient.mk I r) • (a • m)
      rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_smul]⟩
    exact Module.Finite.of_restrictScalars_finite R (R ⧸ I) M

/-- The actual homology sheaf has finite global sections over the quotient ring. -/
public theorem closedImmersionRightAdjointQuotientResolutionHomology_finite (n : ℤ) :
    Module.Finite (R ⧸ I) (moduleSpecΓFunctor.obj
      ((closedImmersionRightAdjointQuotientResolutionComplex I J).homology n)) := by
  let M := (((moduleSpecΓFunctor (R := .of (R ⧸ I))).mapHomologicalComplex (.up ℤ)).obj
    (closedImmersionRightAdjointQuotientResolutionComplex I J)).homology n
  let : Module.Finite (R ⧸ I) M :=
    closedImmersionRightAdjointQuotientResolutionSectionsHomology_finite I J n
  exact Module.Finite.equiv
    ((tilde.isoTop M) ≪≫ moduleSpecΓFunctor.mapIso
      (closedImmersionRightAdjointQuotientResolutionHomologyIso I J n)).toLinearEquiv

/-- Over the Noetherian quotient, homology is an actual affine coherent sheaf:
it is quasicoherent and has finite global sections. -/
public theorem closedImmersionRightAdjointQuotientResolutionHomology_affineFiniteSheaf (n : ℤ) :
    QuasiCoherent.affineFiniteSheaf (.of (R ⧸ I))
      ((closedImmersionRightAdjointQuotientResolutionComplex I J).homology n) :=
  ⟨closedImmersionRightAdjointQuotientResolutionHomology_quasicoherent I J n,
    closedImmersionRightAdjointQuotientResolutionHomology_finite I J n⟩

/-- The coherent homology sheaf has a genuine finite-presentation structure. -/
public theorem closedImmersionRightAdjointQuotientResolutionHomology_finitePresentation (n : ℤ) :
    ((closedImmersionRightAdjointQuotientResolutionComplex I J).homology
      n).IsFinitePresentation := by
  let M := (((moduleSpecΓFunctor (R := .of (R ⧸ I))).mapHomologicalComplex (.up ℤ)).obj
    (closedImmersionRightAdjointQuotientResolutionComplex I J)).homology n
  let : Module.Finite (R ⧸ I) M :=
    closedImmersionRightAdjointQuotientResolutionSectionsHomology_finite I J n
  exact (SheafOfModules.isFinitePresentation (Spec (.of (R ⧸ I))).ringCatSheaf).prop_of_iso
    (closedImmersionRightAdjointQuotientResolutionHomologyIso I J n)
    (finitePresentation_tilde (.of (R ⧸ I)) M)

end FiniteCoefficient

/-- A finitely presented ambient coefficient supplies the required finite sections,
and hence finitely presented homology of the same closed-adjoint resolution. -/
public theorem
    closedImmersionRightAdjointQuotientResolutionHomology_finitePresentation_of_coefficient
    {R : CommRingCat.{u}} [IsNoetherianRing R] (I : Ideal R)
    {L : (Spec R).Modules} [L.IsFinitePresentation] (J : InjectiveResolution L) (n : ℤ) :
    ((closedImmersionRightAdjointQuotientResolutionComplex I J).homology
      n).IsFinitePresentation := by
  let : Module.Finite R (moduleSpecΓFunctor.obj L) :=
    finite_globalSections_of_finitePresentation R L
  exact closedImmersionRightAdjointQuotientResolutionHomology_finitePresentation I J n

end AlgebraicGeometry.Scheme.Modules
