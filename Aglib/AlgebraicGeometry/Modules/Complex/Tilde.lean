/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.TildeExact
public import Aglib.AlgebraicGeometry.Modules.Complex.Sections
public import Aglib.Algebra.Category.ModuleCat.Localization.Homology
public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.QuasiIso

/-!
# The actual affine tilde–global-sections counit on complexes

The original affine adjunction counit is applied termwise through native
complex functors. Its components and section-unit normalization are the
original `fromTildeΓ` maps. Exactness of native tilde supplies the canonical
homology comparison; when this actual counit is a quasi-isomorphism, it
computes the original homology sheaves by their affine module complex.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open AlgebraicGeometry TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules.Complex

universe u w

variable (R : CommRingCat.{u}) {ι : Type w} (d : ComplexShape ι)

/-- Original affine module sections, with their native coordinate-ring action. -/
abbrev specSectionsFunctor (U : (Spec R).Opens) : (Spec R).Modules ⥤ ModuleCat.{u} R :=
  modulesSpecToSheaf ⋙ TopCat.Sheaf.forget _ _ ⋙
    (CategoryTheory.evaluation _ _).obj (op U)

instance specSectionsFunctor_additive (U : (Spec R).Opens) :
    (specSectionsFunctor R U).Additive where
  map_add := by intros; rfl

/-- Original affine-coordinate sections are native variable-ring evaluation followed by
the original structural ring restriction. -/
def specSectionsFunctorIsoEvaluation (U : (Spec R).Opens) :
    specSectionsFunctor R U ≅
      SheafOfModules.evaluation (Spec R).ringCatSheaf (op U) ⋙
        ModuleCat.restrictScalars (((Spec R).presheaf.map (homOfLE le_top).op).hom.comp
          (Scheme.ΓSpecIso R).inv.hom) :=
  Iso.refl _

/-- The original restriction from top sections to sections on an actual affine open. -/
def specSectionsRestriction (U : (Spec R).Opens) :
    moduleSpecΓFunctor (R := R) ⟶ specSectionsFunctor R U where
  app M := (modulesSpecToSheaf.obj M).obj.map (homOfLE le_top).op
  naturality _ _ f := ((modulesSpecToSheaf.map f).hom.naturality _).symm

/-- The original top-to-open restriction of an actual module complex. -/
def specSectionsComplexRestriction (U : (Spec R).Opens)
    (K : HomologicalComplex (Spec R).Modules d) :
    (moduleSpecΓFunctor.mapHomologicalComplex d).obj K ⟶
      ((specSectionsFunctor R U).mapHomologicalComplex d).obj K :=
  (NatTrans.mapHomologicalComplex (specSectionsRestriction R U) d).app K

/-- The original basic-open tilde sections are the native localized module. -/
def tildeBasicOpenSectionsIsoApp (r : R) (M : ModuleCat.{u} R) :
    (ModuleCat.restrictScalars (algebraMap R (Localization (Submonoid.powers r)))).obj
        (M.localizedModule (Submonoid.powers r)) ≅
      (specSectionsFunctor R (PrimeSpectrum.basicOpen r)).obj (tilde M) := by
  let e := IsLocalizedModule.linearEquiv (Submonoid.powers r)
    (M.localizedModuleMkLinearMap (Submonoid.powers r))
    (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom
  refine ModuleCat.isoMk e.toAddEquiv.toAddCommGrpIso ?_
  intro a
  ext x
  change a • e x = e ((algebraMap R (Localization (Submonoid.powers r))) a •
    (show M.localizedModule (Submonoid.powers r) from x))
  rw [IsScalarTower.algebraMap_smul, e.map_smul]

theorem tildeBasicOpenSectionsIsoApp_hom_mk (r : R) (M : ModuleCat.{u} R) (m : M) :
    (tildeBasicOpenSectionsIsoApp R r M).hom
        (M.localizedModuleMkLinearMap (Submonoid.powers r) m) =
      tilde.toOpen M (PrimeSpectrum.basicOpen r) m := by
  change (IsLocalizedModule.linearEquiv (Submonoid.powers r)
      (M.localizedModuleMkLinearMap (Submonoid.powers r))
      (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom)
      (M.localizedModuleMkLinearMap (Submonoid.powers r) m) = _
  exact IsLocalizedModule.linearEquiv_apply _ _ _ m

/-- Native localization agrees naturally with the actual basic-open tilde sections. -/
def tildeBasicOpenSectionsIso (r : R) :
    ModuleCat.localizedModuleFunctor (Submonoid.powers r) ⋙
        ModuleCat.restrictScalars (algebraMap R (Localization (Submonoid.powers r))) ≅
      tilde.functor R ⋙ specSectionsFunctor R (PrimeSpectrum.basicOpen r) :=
  NatIso.ofComponents (tildeBasicOpenSectionsIsoApp R r) (by
    intro M N f
    let e := tildeBasicOpenSectionsIsoApp R r M
    let ℓ := e.symm.toLinearEquiv.toLinearMap.comp
      (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom
    let : IsLocalizedModule (Submonoid.powers r) ℓ :=
      IsLocalizedModule.of_linearEquiv (Submonoid.powers r)
        (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom e.symm.toLinearEquiv
    have hℓ (x : M) : ℓ x = M.localizedModuleMkLinearMap (Submonoid.powers r) x := by
      apply e.toLinearEquiv.injective
      change e.hom (e.inv (tilde.toOpen M (PrimeSpectrum.basicOpen r) x)) = _
      rw [← tildeBasicOpenSectionsIsoApp_hom_mk R r M x]
      exact ConcreteCategory.congr_hom e.inv_hom_id _
    apply ModuleCat.hom_ext
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers r)
      ℓ (tilde.toOpen N (PrimeSpectrum.basicOpen r)).hom
    ext x
    simp only [LinearMap.comp_apply, hℓ]
    change (tildeBasicOpenSectionsIsoApp R r N).hom
        (ModuleCat.localizedModuleMap (Submonoid.powers r) f
          (M.localizedModuleMkLinearMap (Submonoid.powers r) x)) =
      (modulesSpecToSheaf.map (tilde.map f)).hom.app (op (PrimeSpectrum.basicOpen r))
        ((tildeBasicOpenSectionsIsoApp R r M).hom
          (M.localizedModuleMkLinearMap (Submonoid.powers r) x))
    rw [show ModuleCat.localizedModuleMap (Submonoid.powers r) f
        (M.localizedModuleMkLinearMap (Submonoid.powers r) x) =
      N.localizedModuleMkLinearMap (Submonoid.powers r) (f x) from
        IsLocalizedModule.map_apply _ _ _ f.hom x,
      tildeBasicOpenSectionsIsoApp_hom_mk, tildeBasicOpenSectionsIsoApp_hom_mk]
    exact (ConcreteCategory.congr_hom (tilde.toOpen_map_app f (PrimeSpectrum.basicOpen r)) x).symm)

instance tildeBasicOpenSections_preservesFiniteLimits (r : R) :
    PreservesFiniteLimits (tilde.functor R ⋙ specSectionsFunctor R (PrimeSpectrum.basicOpen r)) :=
  preservesFiniteLimits_of_natIso (tildeBasicOpenSectionsIso R r)

instance tildeBasicOpenSections_preservesFiniteColimits (r : R) :
    PreservesFiniteColimits
      (tilde.functor R ⋙ specSectionsFunctor R (PrimeSpectrum.basicOpen r)) :=
  preservesFiniteColimits_of_natIso (tildeBasicOpenSectionsIso R r)

instance tildeBasicOpenSections_preservesHomology (r : R) :
    (tilde.functor R ⋙ specSectionsFunctor R (PrimeSpectrum.basicOpen r)).PreservesHomology := by
  infer_instance

/-- The original basic-open section localization map, natural in the affine module. -/
def tildeBasicOpenUnit (r : R) :
    𝟭 (ModuleCat.{u} R) ⟶
      tilde.functor R ⋙ specSectionsFunctor R (PrimeSpectrum.basicOpen r) where
  app M := tilde.toOpen M (PrimeSpectrum.basicOpen r)
  naturality _ _ f := (tilde.toOpen_map_app f (PrimeSpectrum.basicOpen r)).symm

/-- The actual termwise basic-open localization unit on a module complex. -/
def tildeBasicOpenComplexUnit (r : R) (C : HomologicalComplex (ModuleCat.{u} R) d) :
    C ⟶ ((tilde.functor R ⋙
      specSectionsFunctor R (PrimeSpectrum.basicOpen r)).mapHomologicalComplex d).obj C :=
  ModuleCat.localizationComplexUnit (tildeBasicOpenUnit R r) d C

theorem tildeBasicOpenComplexUnit_f (r : R) (C : HomologicalComplex (ModuleCat.{u} R) d)
    (i : ι) :
    (tildeBasicOpenComplexUnit R d r C).f i = tilde.toOpen (C.X i) (PrimeSpectrum.basicOpen r) :=
  rfl

/-- Homology of the original actual basic-open unit is localization in every shape and degree. -/
theorem tildeBasicOpenComplexUnit_homology_isLocalized (r : R)
    (C : HomologicalComplex (ModuleCat.{u} R) d) (i : ι) :
    IsLocalizedModule (Submonoid.powers r)
      (homologyMap (tildeBasicOpenComplexUnit R d r C) i).hom :=
  ModuleCat.isLocalizedModule_homologyMap_localizationComplexUnit (Submonoid.powers r)
    (tildeBasicOpenUnit R r)
    (fun M => inferInstanceAs
      (IsLocalizedModule.Away r (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom)) d C i

/-- The original affine tilde–sections counit applied to an actual module complex. -/
def tildeGlobalSectionsCounit (K : HomologicalComplex (Spec R).Modules d) :
    ((tilde.functor R).mapHomologicalComplex d).obj
        ((moduleSpecΓFunctor.mapHomologicalComplex d).obj K) ⟶ K :=
  (Functor.mapHomologicalComplexCompIso
      (Iso.refl (moduleSpecΓFunctor ⋙ tilde.functor R)) d).hom.app K ≫
    (NatTrans.mapHomologicalComplex (fromTildeΓNatTrans (R := R)) d).app K ≫
      (Functor.mapHomologicalComplexIdIso (Spec R).Modules d).hom.app K

/-- Every component is the original affine adjunction counit. -/
theorem tildeGlobalSectionsCounit_f (K : HomologicalComplex (Spec R).Modules d) (i : ι) :
    (tildeGlobalSectionsCounit R d K).f i = (K.X i).fromTildeΓ := by
  simp only [tildeGlobalSectionsCounit, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f, Iso.refl_hom,
    NatTrans.mapHomologicalComplex_app_f, Functor.mapHomologicalComplexIdIso_hom_app_f]
  rfl

/-- The termwise actual counit retains the original section-localization unit equation. -/
theorem tildeGlobalSectionsCounit_toOpen (K : HomologicalComplex (Spec R).Modules d)
    (i : ι) (U : (Spec R).Opens) :
    tilde.toOpen (moduleSpecΓFunctor.obj (K.X i)) U ≫
        (modulesSpecToSheaf.map ((tildeGlobalSectionsCounit R d K).f i)).hom.app (op U) =
      (modulesSpecToSheaf.obj (K.X i)).obj.map (homOfLE le_top).op := by
  rw [tildeGlobalSectionsCounit_f]
  exact toOpen_fromTildeΓ_app (K.X i) U

/-- The original localization unit followed by the actual counit is the original section
restriction, as an equality of actual chain maps. -/
theorem tildeBasicOpenComplexUnit_counit (r : R)
    (K : HomologicalComplex (Spec R).Modules d) :
    tildeBasicOpenComplexUnit R d r ((moduleSpecΓFunctor.mapHomologicalComplex d).obj K) ≫
        ((specSectionsFunctor R (PrimeSpectrum.basicOpen r)).mapHomologicalComplex d).map
          (tildeGlobalSectionsCounit R d K) =
      specSectionsComplexRestriction R d (PrimeSpectrum.basicOpen r) K := by
  ext i : 1
  simp only [HomologicalComplex.comp_f, tildeBasicOpenComplexUnit_f]
  exact tildeGlobalSectionsCounit_toOpen R d K i (PrimeSpectrum.basicOpen r)

/-- Localization of the actual section restriction makes the homology map of the original
counit invertible on this principal open. -/
theorem tildeGlobalSectionsCounit_homology_isIso_on_basicOpen (r : R)
    (K : HomologicalComplex (Spec R).Modules d) (i : ι)
    (hlocal : IsLocalizedModule (Submonoid.powers r)
      (homologyMap (specSectionsComplexRestriction R d (PrimeSpectrum.basicOpen r) K) i).hom) :
    IsIso (homologyMap
      (((specSectionsFunctor R (PrimeSpectrum.basicOpen r)).mapHomologicalComplex d).map
        (tildeGlobalSectionsCounit R d K)) i) := by
  apply ModuleCat.isIso_of_isLocalizedModule_comp
    (tildeBasicOpenComplexUnit_homology_isLocalized R d r
      ((moduleSpecΓFunctor.mapHomologicalComplex d).obj K) i)
  rw [← homologyMap_comp, tildeBasicOpenComplexUnit_counit]
  exact hlocal

/-- The original affine counit is a quasi-isomorphism when actual section-cohomology
restrictions are the original localization maps on every principal open. -/
theorem tildeGlobalSectionsCounit_quasiIso_of_isLocalized
    (K : CochainComplex (Spec R).Modules ℤ)
    (hlocal : ∀ r : R, ∀ i : ℤ, IsLocalizedModule (Submonoid.powers r)
      (homologyMap
        (specSectionsComplexRestriction R (.up ℤ) (PrimeSpectrum.basicOpen r) K) i).hom) :
    QuasiIso (tildeGlobalSectionsCounit R (.up ℤ) K) := by
  apply quasiIso_of_sections_on_basis _ PrimeSpectrum.isBasis_basic_opens
  rintro _ ⟨r, rfl⟩
  let U := PrimeSpectrum.basicOpen r
  let E := SheafOfModules.evaluation.{u} (Spec R).ringCatSheaf (op U)
  let G := ModuleCat.restrictScalars
    (((Spec R).presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.comp
      (Scheme.ΓSpecIso R).inv.hom)
  apply (quasiIso_map_iff_of_preservesHomology
    ((E.mapHomologicalComplex (.up ℤ)).map
      (tildeGlobalSectionsCounit R (.up ℤ) K)) G).mp
  change QuasiIso (((specSectionsFunctor R U).mapHomologicalComplex (.up ℤ)).map
    (tildeGlobalSectionsCounit R (.up ℤ) K))
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact tildeGlobalSectionsCounit_homology_isIso_on_basicOpen R (.up ℤ) r K i (hlocal r i)

/-- The actual counit chain map is natural in every original module chain map. -/
@[reassoc]
theorem tildeGlobalSectionsCounit_naturality
    {K L : HomologicalComplex (Spec R).Modules d} (φ : K ⟶ L) :
    ((tilde.functor R).mapHomologicalComplex d).map
        ((moduleSpecΓFunctor.mapHomologicalComplex d).map φ) ≫
        tildeGlobalSectionsCounit R d L = tildeGlobalSectionsCounit R d K ≫ φ := by
  ext i : 1
  simp only [HomologicalComplex.comp_f, tildeGlobalSectionsCounit_f]
  exact fromTildeΓNatTrans.naturality (φ.f i)

/-- Exact native tilde identifies affine module-complex homology with the original homology
sheaf through the homology map of the actual counit. -/
def tildeGlobalSectionsHomologyIso (K : HomologicalComplex (Spec R).Modules d)
    [QuasiIso (tildeGlobalSectionsCounit R d K)] (i : ι) :
    tilde (((moduleSpecΓFunctor.mapHomologicalComplex d).obj K).homology i) ≅ K.homology i :=
  ((((moduleSpecΓFunctor.mapHomologicalComplex d).obj K).sc i).mapHomologyIso
    (tilde.functor R)).symm ≪≫ asIso (homologyMap (tildeGlobalSectionsCounit R d K) i)

/-- The affine homology computation has the native exact-tilde and actual-counit forward map. -/
theorem tildeGlobalSectionsHomologyIso_hom (K : HomologicalComplex (Spec R).Modules d)
    [QuasiIso (tildeGlobalSectionsCounit R d K)] (i : ι) :
    (tildeGlobalSectionsHomologyIso R d K i).hom =
      ((((moduleSpecΓFunctor.mapHomologicalComplex d).obj K).sc i).mapHomologyIso
        (tilde.functor R)).inv ≫ homologyMap (tildeGlobalSectionsCounit R d K) i := rfl

/-- Invertibility of the actual affine counit computes a quasicoherent original homology sheaf. -/
theorem quasicoherent_homology_of_tildeGlobalSectionsCounit
    (K : HomologicalComplex (Spec R).Modules d) [QuasiIso (tildeGlobalSectionsCounit R d K)]
    (i : ι) : (K.homology i).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
    (tildeGlobalSectionsHomologyIso R d K i) inferInstance

end AlgebraicGeometry.Scheme.Modules.Complex
