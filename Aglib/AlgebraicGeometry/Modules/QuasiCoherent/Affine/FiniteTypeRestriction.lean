/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Exact
public import Aglib.Algebra.Category.ModuleCat.FiniteLocalization
public import Aglib.AlgebraicGeometry.Modules.Exact
/-! # Actual principal-open restriction of affine finite-type sheaves -/
@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ModuleCat
open scoped ModuleCat.Algebra
attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent
variable (R : CommRingCat.{u}) (r : R)

/-- The actual principal-open immersion `Spec R[1/r] ⟶ Spec R`. -/
abbrev principalOpen : Spec (CommRingCat.of (Localization.Away r)) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))

/-- Actual global sections after restricting the actual associated sheaf. -/
abbrev restrictionGlobalSections (M : ModuleCat.{u} R) : ModuleCat.{u} (Localization.Away r) :=
  moduleSpecΓFunctor.obj ((Scheme.Modules.restrictFunctor (principalOpen R r)).obj (tilde M))

/-- The restriction-section isomorphism is linear over the original ring. -/
def restrictionGlobalSectionsEquiv (M : ModuleCat.{u} R) :
    restrictionGlobalSections R r M ≃ₗ[R]
      (modulesSpecToSheaf.obj (tilde M)).presheaf.obj
        (.op (principalOpen R r ''ᵁ ⊤)) where
  __ := AddEquiv.refl _
  map_smul' a m := _root_.AlgebraicGeometry.Scheme.Modules.restrictAppIso_smul_Spec
    (CommRingCat.ofHom (algebraMap R (Localization.Away r))) a m

/-- The localization map from a module into sections on its principal open. -/
def toRestrictionGlobalSections (M : ModuleCat.{u} R) :
    M →ₗ[R] restrictionGlobalSections R r M :=
  (restrictionGlobalSectionsEquiv R r M).symm.toLinearMap.comp
    (tilde.toOpen M (principalOpen R r ''ᵁ ⊤)).hom

instance restrictionGlobalSections_isLocalized (M : ModuleCat.{u} R) :
    IsLocalizedModule.Away r (toRestrictionGlobalSections R r M) := by
  have : IsLocalizedModule.Away r (tilde.toOpen M (principalOpen R r ''ᵁ ⊤)).hom := by
    have he : principalOpen R r ''ᵁ ⊤ = PrimeSpectrum.basicOpen r := by
      rw [Scheme.Hom.image_top_eq_opensRange]
      exact Scheme.Hom.opensRange_localizationAway r
    rw [he]
    infer_instance
  exact IsLocalizedModule.of_linearEquiv (Submonoid.powers r) _
    (restrictionGlobalSectionsEquiv R r M).symm

/-- The localized module and the actual sections of the restricted sheaf
are canonically isomorphic as modules over the localized ring. -/
def localizationRestrictionIso (M : ModuleCat.{u} R) :
    M.localizedModule (Submonoid.powers r) ≅ restrictionGlobalSections R r M :=
  ((IsLocalizedModule.linearEquiv (Submonoid.powers r)
    (M.localizedModuleMkLinearMap (Submonoid.powers r))
    (toRestrictionGlobalSections R r M)).extendScalarsOfIsLocalization
      (Submonoid.powers r) (Localization.Away r)).toModuleIso

@[simp]
lemma localizationRestrictionIso_hom_apply (M : ModuleCat.{u} R) (x : M) :
    (localizationRestrictionIso R r M).hom (M.localizedModuleMkLinearMap (Submonoid.powers r) x) =
      toRestrictionGlobalSections R r M x :=
  IsLocalizedModule.linearEquiv_apply _ _ _ x

/-- The actual functor of sections after restricting associated sheaves. -/
abbrev restrictionGlobalSectionsFunctor : ModuleCat.{u} R ⥤ ModuleCat.{u} (Localization.Away r) :=
  (tilde.functor R ⋙ Scheme.Modules.restrictFunctor (principalOpen R r)) ⋙ moduleSpecΓFunctor

lemma toRestrictionGlobalSections_natural {M N : ModuleCat.{u} R} (f : M ⟶ N) (x : M) :
    ((restrictionGlobalSectionsFunctor R r).map f) (toRestrictionGlobalSections R r M x) =
      toRestrictionGlobalSections R r N (f x) := by
  exact ConcreteCategory.congr_hom
    (tilde.toOpen_map_app f (principalOpen R r ''ᵁ ⊤)) x

/-- Actual localization agrees naturally with global sections of actual
principal-open restriction of associated sheaves. -/
def localizationRestrictionNatIso :
    ModuleCat.localizedModuleFunctor (Submonoid.powers r) ≅
      restrictionGlobalSectionsFunctor R r :=
  NatIso.ofComponents (localizationRestrictionIso R r) (by
    intro M N f
    let : Module R (M.localizedModule (Submonoid.powers r)) :=
      ModuleCat.instModuleCarrierLocalizationLocalizedModule M (Submonoid.powers r)
    apply ModuleCat.hom_ext
    change (ModuleCat.localizedModuleMap (Submonoid.powers r) f ≫
      (localizationRestrictionIso R r N).hom).hom =
      ((localizationRestrictionIso R r M).hom ≫
        (restrictionGlobalSectionsFunctor R r).map f).hom
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers r)
      (M.localizedModuleMkLinearMap (Submonoid.powers r))
      (toRestrictionGlobalSections R r N)
    ext x
    change (localizationRestrictionIso R r N).hom
      (ModuleCat.localizedModuleMap (Submonoid.powers r) f
        (M.localizedModuleMkLinearMap (Submonoid.powers r) x)) =
      ((restrictionGlobalSectionsFunctor R r).map f)
        ((localizationRestrictionIso R r M).hom
          (M.localizedModuleMkLinearMap (Submonoid.powers r) x))
    have h : ModuleCat.localizedModuleMap (Submonoid.powers r) f
        (M.localizedModuleMkLinearMap (Submonoid.powers r) x) =
        N.localizedModuleMkLinearMap (Submonoid.powers r) (f x) :=
      IsLocalizedModule.map_apply _ _ _ f.hom x
    rw [h, localizationRestrictionIso_hom_apply, localizationRestrictionIso_hom_apply]
    exact (toRestrictionGlobalSections_natural R r f x).symm)

/-- The canonical affine equivalence intertwines actual principal-open
restriction and actual scalar localization, on all quasicoherent sheaves. -/
def principalRestrictionGlobalSectionsIso :
    (tildeEquiv (R := R)).inverse ⋙ ModuleCat.localizedModuleFunctor (Submonoid.powers r) ≅
      ((SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι ⋙
        Scheme.Modules.restrictFunctor (principalOpen R r)) ⋙ moduleSpecΓFunctor :=
  Functor.isoWhiskerLeft _ (localizationRestrictionNatIso R r) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (Functor.associator _ _ _).symm _ ≪≫
    Functor.isoWhiskerRight
      (Functor.isoWhiskerRight (affineQuasicoherentToSheavesIso R) _) _

/-- The actual restriction on the full quasicoherent sheaf categories. -/
def affineQuasicoherentRestriction :
    AffineQuasicoherent R ⥤ AffineQuasicoherent (CommRingCat.of (Localization.Away r)) :=
  (SheafOfModules.isQuasicoherent (Spec (CommRingCat.of (Localization.Away r))).ringCatSheaf).lift
    ((SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ι ⋙
      Scheme.Modules.restrictFunctor (principalOpen R r))
    (fun M => by
      have : M.obj.IsQuasicoherent := M.property
      exact Scheme.Modules.isQuasicoherent_restrictFunctor (principalOpen R r) M.obj)

variable [IsNoetherianRing R]

omit [IsNoetherianRing R] in
/-- Actual principal-open restriction preserves affine finite-type quasicoherent sheaves. -/
lemma affineFiniteType_restriction (M : AffineFiniteType R) :
    affineFiniteType (CommRingCat.of (Localization.Away r))
      ((affineQuasicoherentRestriction R r).obj M.obj) := by
  have : Module.Finite (Localization.Away r)
      (((tildeEquiv (R := R)).inverse ⋙
        ModuleCat.localizedModuleFunctor (Submonoid.powers r)).obj M.obj) :=
    ((ModuleCat.FiniteLocalization.functor (Submonoid.powers r)).obj
      ((affineFiniteTypeModuleEquivalence R).functor.obj M)).property
  exact Module.Finite.equiv ((principalRestrictionGlobalSectionsIso R r).app M.obj).toLinearEquiv

/-- Principal-open restriction of finite-type quasicoherent sheaves. Its underlying
sheaf functor is actual geometric restriction by definition. -/
def affinePrincipalRestriction :
    AffineFiniteType R ⥤ AffineFiniteType (CommRingCat.of (Localization.Away r)) :=
  (affineFiniteType (CommRingCat.of (Localization.Away r))).lift
    ((affineFiniteType R).ι ⋙ affineQuasicoherentRestriction R r)
    (affineFiniteType_restriction R r)

omit [IsNoetherianRing R] in
/-- The restriction functor on finite-type quasicoherent sheaves has the expected
underlying geometric sheaf functor. -/
theorem affinePrincipalRestriction_comp_inclusion :
    affinePrincipalRestriction R r ⋙ affineFiniteTypeToModules (CommRingCat.of (Localization.Away
      r))
      =
      affineFiniteTypeToModules R ⋙ Scheme.Modules.restrictFunctor (principalOpen R r) := rfl

/-- The actual restriction/localization square on finite-type quasicoherent sheaves,
as a natural isomorphism of finite-module-valued functors. -/
def affinePrincipalRestrictionSquare :
    (affineFiniteTypeModuleEquivalence R).functor ⋙
      ModuleCat.FiniteLocalization.functor
      (Submonoid.powers r) ≅
      affinePrincipalRestriction R r ⋙
        (affineFiniteTypeModuleEquivalence (CommRingCat.of (Localization.Away r))).functor :=
  ((finiteModule (Localization.Away r)).fullyFaithfulι.whiskeringRight _).preimageIso
    (Functor.isoWhiskerLeft (affineFiniteType R).ι (principalRestrictionGlobalSectionsIso R r))

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
