/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.DerivedModel
public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Affine.Single
public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.GlobalSectionsComposition
public import Aglib.AlgebraicGeometry.Modules.Complex.Tilde.HomologyMap
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Injective
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.Adjunction.InjectiveResolution

/-!
# Original affine direct-image derived Hom

For a qcqs map to a spectrum and quasicoherent source and target coefficients,
actual derived global sections give an additive Hom equivalence. Its inverse
uses the original affine direct-image model of the same injective resolution.
The forward formula is the original derived global-sections composition,
followed by actual derived sections of the arbitrary input arrow and the
original affine acyclic-single and shift comparisons. Pushed injective terms
are not assumed quasicoherent or injective.
-/

@[expose] public section
noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor HomologicalComplex
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- The standard derived-category model for modules on `X`, used locally. -/
local instance affineDerivedHomSchemeCategory (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
/-- The standard derived-category model for `A`-modules, used locally. -/
local instance affineDerivedHomModuleCategory (A : CommRingCat.{u}) :
    HasDerivedCategory.{u + 1} (ModuleCat.{u} A) := HasDerivedCategory.standard _

private def homIsoAddEquiv {C : Type*} [Category* C] [Preadditive C]
    {X X' Y Y' : C} (e : X ≅ X') (d : Y ≅ Y') :
    (X ⟶ Y) ≃+ (X' ⟶ Y') :=
  { Iso.homCongr e d with
    map_add' f g := by
      simp [Iso.homCongr_apply, Preadditive.comp_add, Preadditive.add_comp] }

@[simp] private theorem homIsoAddEquiv_apply {C : Type*} [Category* C] [Preadditive C]
    {X X' Y Y' : C} (e : X ≅ X') (d : Y ≅ Y') (f : X ⟶ Y) :
    homIsoAddEquiv e d f = e.inv ≫ f ≫ d.hom := rfl

private def coefficientShiftIso {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (N : C) (n q : ℤ) :
    ((DerivedCategory.singleFunctor C n).obj N)⟦q⟧ ≅
      ((DerivedCategory.singleFunctor C 0).obj N)⟦q - n⟧ :=
  ((DerivedCategory.singleFunctors C).shiftIso q (n - q) n (by omega)).app N ≪≫
    (((DerivedCategory.singleFunctors C).shiftIso (q - n) (n - q) 0 (by omega)).app N).symm

private theorem shifted_map_pre_post {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] (H : C ⥤ D) [H.CommShift ℤ]
    {X' X Y Y' : C} (a : X' ⟶ X) {k : ℤ} (b : ShiftedHom X Y k) (c : Y ⟶ Y') :
    ShiftedHom.map (show ShiftedHom X' Y' k from a ≫ b ≫ c⟦k⟧') H =
      H.map a ≫ b.map H ≫ (H.map c)⟦k⟧' := by
  rw [← ShiftedHom.mk₀_comp (0 : ℤ) rfl a,
    ← ShiftedHom.comp_mk₀ b (0 : ℤ) rfl c,
    ShiftedHom.map_comp, ShiftedHom.map_comp, ShiftedHom.map_mk₀,
    ShiftedHom.map_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]

private theorem shifted_map_iso {C D : Type*} [Category* C] [Category* D]
    [HasShift C ℤ] [HasShift D ℤ] {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (e : F ≅ G) [NatTrans.CommShift e.hom ℤ] {X Y : C} {k : ℤ}
    (b : ShiftedHom X Y k) :
    b.map F = e.hom.app X ≫ b.map G ≫ (e.inv.app Y)⟦k⟧' := by
  simpa only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀] using
    (ShiftedHom.map_naturality_2 b e).symm

private theorem derived_map_surjective {C : Type*} [Category* C] [Abelian C]
    [HasDerivedCategory C] (K L : CochainComplex C ℤ) [L.IsKInjective] :
    Function.Surjective (fun p : K ⟶ L => DerivedCategory.Q.map p) := by
  intro f
  obtain ⟨p, rfl⟩ := (CochainComplex.homotopyDerivedHomEquiv K L).surjective f
  obtain ⟨q, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective p
  exact ⟨q, (CochainComplex.homotopyDerivedHomEquiv_map K L q).symm⟩

private def specStructuralSectionsIso (A : CommRingCat.{u}) :
    moduleGlobalSectionsFunctorOfHom (Spec A) (Scheme.ΓSpecIso A).inv.hom ≅
      moduleSpecΓFunctor :=
  NatIso.ofComponents
    (fun N => (moduleTopSectionsIso (Spec A) (Scheme.ΓSpecIso A).inv.hom N).symm)
    (by intro M N f; ext x; rfl)

private def nativeSectionsCompIso {A : CommRingCat.{u}} {X : Scheme.{u}}
    (p : X ⟶ Spec A) :
    (moduleGlobalSectionsFunctorOfHom X
      (p.appTop.hom.comp (Scheme.ΓSpecIso A).inv.hom)).rightDerivedFunctorPlus ≅
      (Scheme.Modules.pushforward p).rightDerivedFunctorPlus ⋙
        moduleSpecΓFunctor.rightDerivedFunctorPlus :=
  moduleDerivedGlobalSectionsPushforwardCompIso p (Scheme.ΓSpecIso A).inv.hom ≪≫
    isoWhiskerLeft (Scheme.Modules.pushforward p).rightDerivedFunctorPlus
      ((moduleGlobalSectionsFunctorOfHom (Spec A)
        (Scheme.ΓSpecIso A).inv.hom).rightDerivedFunctorPlusIso
         (specStructuralSectionsIso A))

private def affineCoefficientIso {A : CommRingCat.{u}} (N : (Spec A).Modules)
    [N.IsQuasicoherent] :
    moduleSpecΓFunctor.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor (Spec A).Modules 0).obj N) ≅
      (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).obj
        (moduleSpecΓFunctor.obj N) :=
  moduleSpecΓFunctor.rightDerivedFunctorPlusSingleIsoOfAcyclic N
    (AffineDerived.isZero_rightDerived_globalSections_succ N)

private def affineTildeHomEquiv {A : CommRingCat.{u}}
    (P : CochainComplex.Plus (ModuleCat.{u} A))
    (N : (Spec A).Modules) [N.IsQuasicoherent] (k : ℤ) :
    (DerivedCategory.Q.obj (((tilde.functor A).mapHomologicalComplex (.up ℤ)).obj P.obj) ⟶
      ((DerivedCategory.singleFunctor (Spec A).Modules 0).obj N)⟦k⟧) ≃+
    (DerivedCategory.Q.obj P.obj ⟶
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (moduleSpecΓFunctor.obj N))⟦k⟧) :=
  (homIsoAddEquiv (Iso.refl _) (CategoryTheory.Adjunction.resolutionShiftIso
      (injectiveResolution N) k)).trans
    (((tilde.adjunction (R := A)).cochainDerivedHomEquivOfInjectiveResolution
        (injectiveResolution N) k P.obj).trans
      (homIsoAddEquiv (Iso.refl _)
        (CategoryTheory.Adjunction.rightDerivedResolutionShiftIso
          (G := moduleSpecΓFunctor) (injectiveResolution N) k ≪≫
        (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) k).mapIso
          (DerivedCategory.Plus.ι.mapIso (affineCoefficientIso N)))))

private theorem resolutionShiftSections {A : CommRingCat.{u}}
    {N : (Spec A).Modules} (J : InjectiveResolution N)
    (K : CochainComplex.Plus (Spec A).Modules) (k : ℤ)
    (B : ShiftedHom K J.cochainComplexPlus k) :
    DerivedCategory.Q.map ((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).map
        (B.map (CochainComplex.Plus.ι (Spec A).Modules))) ≫
      (CategoryTheory.Adjunction.rightDerivedResolutionShiftIso
        (G := moduleSpecΓFunctor) J k).hom =
    (DerivedCategory.Plus.QCompιIso (ModuleCat.{u} A)).inv.app
        (moduleSpecΓFunctor.mapCochainComplexPlus.obj K) ≫
      B.map (moduleSpecΓFunctor.mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι) ≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) k).map
        (DerivedCategory.Plus.ι.map (J.rightDerivedFunctorPlusIso moduleSpecΓFunctor).hom) := by
  have hraw : DerivedCategory.Q.map
      ((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).map
        (B.map (CochainComplex.Plus.ι (Spec A).Modules))) ≫
      (CategoryTheory.Adjunction.rightDerivedResolutionShiftIso
        (G := moduleSpecΓFunctor) J k).hom =
      ((B.map (CochainComplex.Plus.ι (Spec A).Modules)).map
        (moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ))).map DerivedCategory.Q ≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) k).map
        (CategoryTheory.Adjunction.rightDerivedResolutionIso
          (G := moduleSpecΓFunctor) J).hom := by
    simp only [CategoryTheory.Adjunction.rightDerivedResolutionShiftIso,
      Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, ShiftedHom.map,
      Functor.map_comp, Category.assoc]
    rfl
  have hG := shifted_map_iso moduleSpecΓFunctor.mapCochainComplexPlusCompι B
  simp only [ShiftedHom.comp_map, Functor.mapCochainComplexPlusCompι_hom_app,
    Functor.mapCochainComplexPlusCompι_inv_app] at hG
  erw [Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id] at hG
  have hQ := shifted_map_iso (DerivedCategory.Plus.QCompιIso (ModuleCat.{u} A))
    (B.map moduleSpecΓFunctor.mapCochainComplexPlus)
  simp only [ShiftedHom.comp_map] at hQ
  rw [hG] at hQ
  rw [hraw]
  simp only [ShiftedHom.comp_map]
  rw [hQ]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  rw [← (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) k).map_comp]
  rfl

section Affine
variable {A : CommRingCat.{u}} {X : Scheme.{u}}
  (p : X ⟶ Spec A) [QuasiCompact p] [QuasiSeparated p]
  (M : X.Modules) [M.IsQuasicoherent]

private abbrev sourceSections :=
  moduleGlobalSectionsFunctorOfHom X (p.appTop.hom.comp (Scheme.ΓSpecIso A).inv.hom)

private def sourceModel : CochainComplex.Plus (ModuleCat.{u} A) :=
  (sourceSections p).mapCochainComplexPlus.obj (injectiveResolution M).cochainComplexPlus

private def affineModelIso :
    DerivedCategory.Q.obj (((tilde.functor A).mapHomologicalComplex (.up ℤ)).obj
      (sourceModel p M).obj) ≅
    DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedPushforwardPlus p).obj
      ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) :=
  (DerivedCategory.Plus.QCompιIso (Spec A).Modules).symm.app
      ((tilde.functor A).mapCochainComplexPlus.obj (sourceModel p M)) ≪≫
    DerivedCategory.Plus.ι.mapIso
      (moduleSpecDerivedPushforwardModelIso p (injectiveResolution M) (sourceModel p M)
        ((injectiveResolution M).rightDerivedFunctorPlusIso (sourceSections p)))

private def sourceSectionsModelIso :
    DerivedCategory.Q.obj (sourceModel p M).obj ≅
      DerivedCategory.Plus.ι.obj ((sourceSections p).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) :=
  CategoryTheory.Adjunction.rightDerivedResolutionIso (G := sourceSections p)
    (injectiveResolution M)

private def affineHomEquivZero (N : (Spec A).Modules) [N.IsQuasicoherent] (k : ℤ) :
    (DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedPushforwardPlus p).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) ⟶
      ((DerivedCategory.singleFunctor (Spec A).Modules 0).obj N)⟦k⟧) ≃+
    (DerivedCategory.Plus.ι.obj ((sourceSections p).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) ⟶
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (moduleSpecΓFunctor.obj N))⟦k⟧) :=
  (homIsoAddEquiv (affineModelIso p M).symm (Iso.refl _)).trans
    ((affineTildeHomEquiv (sourceModel p M) N k).trans
      (homIsoAddEquiv (sourceSectionsModelIso p M) (Iso.refl _)))

private theorem affineHomEquivZero_apply (N : (Spec A).Modules) [N.IsQuasicoherent]
    (k : ℤ)
    (a : DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedPushforwardPlus p).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) ⟶
      ((DerivedCategory.singleFunctor (Spec A).Modules 0).obj N)⟦k⟧) :
    affineHomEquivZero p M N k a =
      (sourceSectionsModelIso p M).inv ≫
        (tilde.adjunction (R := A)).cochainDerivedHomEquivOfInjectiveResolution
          (injectiveResolution N) k (sourceModel p M).obj
          ((affineModelIso p M).hom ≫ a ≫
            (CategoryTheory.Adjunction.resolutionShiftIso (injectiveResolution N) k).hom) ≫
        (CategoryTheory.Adjunction.rightDerivedResolutionShiftIso
          (G := moduleSpecΓFunctor) (injectiveResolution N) k).hom ≫
        (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) k).map
          (DerivedCategory.Plus.ι.map (affineCoefficientIso N).hom) := by
  simp only [affineHomEquivZero, affineTildeHomEquiv,
    AddEquiv.trans_apply, homIsoAddEquiv_apply, Iso.symm_inv, Iso.refl_hom,
    Iso.refl_inv, Category.id_comp, Category.comp_id, Iso.trans_hom,
    Functor.mapIso_hom, Category.assoc]

private theorem affineModelIso_hom :
    (affineModelIso p M).hom =
      DerivedCategory.Q.map
        (((tilde.functor A).mapHomologicalComplex (.up ℤ)).map
          (moduleSpecPushforwardGlobalSectionsComplexIso p (.up ℤ)
            (injectiveResolution M).cochainComplex).inv ≫
        Scheme.Modules.Complex.tildeGlobalSectionsCounit A (.up ℤ)
          (((Scheme.Modules.pushforward p).mapHomologicalComplex (.up ℤ)).obj
            (injectiveResolution M).cochainComplex)) ≫
      (CategoryTheory.Adjunction.rightDerivedResolutionIso
        (G := Scheme.Modules.pushforward p) (injectiveResolution M)).hom := by
  let I := injectiveResolution M
  let P := sourceModel p M
  let S := moduleSpecΓFunctor.mapCochainComplexPlus.obj
    ((Scheme.Modules.pushforward p).mapCochainComplexPlus.obj I.cochainComplexPlus)
  let c := moduleResolutionPushforwardSectionsPlusIso p I
  have hc : (moduleSpecDerivedModelSectionsIso p I P
      (I.rightDerivedFunctorPlusIso (sourceSections p))).hom =
        DerivedCategory.Plus.Q.map c.inv := by
    simp only [moduleSpecDerivedModelSectionsIso, Iso.trans_hom, Iso.symm_hom,
      Functor.mapIso_hom, Iso.hom_inv_id_assoc]
    rfl
  have hu := (tilde.functor A).rightDerivedFunctorPlusUnit.naturality c.inv
  simp only [Functor.comp_map] at hu
  have hE : (moduleSpecDerivedPushforwardModelIso p I P
      (I.rightDerivedFunctorPlusIso (sourceSections p))).hom =
      DerivedCategory.Plus.Q.map
          ((tilde.functor A).mapCochainComplexPlus.map c.inv ≫
            moduleResolutionPushforwardTildeCounitPlus p I) ≫
        (I.rightDerivedFunctorPlusIso (Scheme.Modules.pushforward p)).hom := by
    dsimp only [moduleSpecDerivedPushforwardModelIso]
    rw [moduleSpecDerivedPushforwardModelIsoOfCounit_hom, hc]
    erw [← reassoc_of% hu]
    simp only [IsIso.hom_inv_id_assoc]
    rw [← Functor.map_comp_assoc]
  let w := (tilde.functor A).mapCochainComplexPlus.map c.inv ≫
    moduleResolutionPushforwardTildeCounitPlus p I
  have hQ := (DerivedCategory.Plus.QCompιIso (Spec A).Modules).inv.naturality w
  change DerivedCategory.Q.map w.hom ≫
      (DerivedCategory.Plus.QCompιIso (Spec A).Modules).inv.app
        ((Scheme.Modules.pushforward p).mapCochainComplexPlus.obj I.cochainComplexPlus) =
    (DerivedCategory.Plus.QCompιIso (Spec A).Modules).inv.app
      ((tilde.functor A).mapCochainComplexPlus.obj P) ≫
        DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map w) at hQ
  change (DerivedCategory.Plus.QCompιIso (Spec A).Modules).inv.app
      ((tilde.functor A).mapCochainComplexPlus.obj P) ≫
        DerivedCategory.Plus.ι.map
          (moduleSpecDerivedPushforwardModelIso p I P
            (I.rightDerivedFunctorPlusIso (sourceSections p))).hom = _
  rw [hE, Functor.map_comp]
  change (DerivedCategory.Plus.QCompιIso (Spec A).Modules).inv.app
      ((tilde.functor A).mapCochainComplexPlus.obj P) ≫
        DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map w) ≫
          DerivedCategory.Plus.ι.map
            (I.rightDerivedFunctorPlusIso (Scheme.Modules.pushforward p)).hom =
    DerivedCategory.Q.map w.hom ≫
      (DerivedCategory.Plus.QCompιIso (Spec A).Modules).inv.app
        ((Scheme.Modules.pushforward p).mapCochainComplexPlus.obj I.cochainComplexPlus) ≫
      DerivedCategory.Plus.ι.map
        (I.rightDerivedFunctorPlusIso (Scheme.Modules.pushforward p)).hom
  simpa only [Category.assoc] using
    hQ.symm =≫ DerivedCategory.Plus.ι.map
      (I.rightDerivedFunctorPlusIso (Scheme.Modules.pushforward p)).hom

omit [QuasiCompact p] [QuasiSeparated p] [M.IsQuasicoherent] in
private theorem nativeSectionsCompIso_unit (I : InjectiveResolution M) :
    (sourceSections p).rightDerivedFunctorPlusUnit.app I.cochainComplexPlus ≫
      (nativeSectionsCompIso p).hom.app (DerivedCategory.Plus.Q.obj I.cochainComplexPlus) =
    DerivedCategory.Plus.Q.map (moduleResolutionPushforwardSectionsPlusIso p I).inv ≫
      moduleSpecΓFunctor.rightDerivedFunctorPlusUnit.app
        ((Scheme.Modules.pushforward p).mapCochainComplexPlus.obj I.cochainComplexPlus) ≫
      moduleSpecΓFunctor.rightDerivedFunctorPlus.map
        ((Scheme.Modules.pushforward p).rightDerivedFunctorPlusUnit.app
          I.cochainComplexPlus) := by
  let H := moduleGlobalSectionsFunctorOfHom (Spec A) (Scheme.ΓSpecIso A).inv.hom
  let J := (Scheme.Modules.pushforward p).mapCochainComplexPlus.obj I.cochainComplexPlus
  let e := H.rightDerivedFunctorPlusIso (specStructuralSectionsIso A)
  have hn := e.hom.naturality
    ((Scheme.Modules.pushforward p).rightDerivedFunctorPlusUnit.app I.cochainComplexPlus)
  dsimp only [nativeSectionsCompIso, Iso.trans_hom, isoWhiskerLeft_hom, NatTrans.comp_app]
  rw [← Category.assoc, moduleDerivedGlobalSectionsPushforwardCompIso_unit]
  rw [Functor.rightDerivedFunctorPlusCompUnit_app]
  simp only [Category.assoc]
  change DerivedCategory.Plus.Q.map
      ((NatIso.mapCochainComplexPlus
        (modulePushforwardGlobalSectionsIso p (Scheme.ΓSpecIso A).inv.hom)).inv.app
          I.cochainComplexPlus) ≫
    H.rightDerivedFunctorPlusUnit.app J ≫
      H.rightDerivedFunctorPlus.map
        ((Scheme.Modules.pushforward p).rightDerivedFunctorPlusUnit.app
          I.cochainComplexPlus) ≫
      e.hom.app ((Scheme.Modules.pushforward p).rightDerivedFunctorPlus.obj
        (DerivedCategory.Plus.Q.obj I.cochainComplexPlus)) = _
  erw [hn]
  have hs := H.rightDerivedFunctorPlusIso_hom_app (specStructuralSectionsIso A) J
  erw [reassoc_of% hs]
  have hc : ((NatIso.mapCochainComplexPlus
        (modulePushforwardGlobalSectionsIso p (Scheme.ΓSpecIso A).inv.hom)).inv.app
          I.cochainComplexPlus) ≫
      (NatIso.mapCochainComplexPlus (specStructuralSectionsIso A)).hom.app J =
      (moduleResolutionPushforwardSectionsPlusIso p I).inv := by
    apply ObjectProperty.hom_ext
    ext n x
    rfl
  rw [← Functor.map_comp_assoc, hc]

omit [QuasiCompact p] [QuasiSeparated p] [M.IsQuasicoherent] in
private theorem sourceSectionsModel_comp :
    ((injectiveResolution M).rightDerivedFunctorPlusIso (sourceSections p)).hom ≫
      (nativeSectionsCompIso p).hom.app
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) =
    DerivedCategory.Plus.Q.map
        (moduleResolutionPushforwardSectionsPlusIso p (injectiveResolution M)).inv ≫
      moduleSpecΓFunctor.rightDerivedFunctorPlusUnit.app
        ((Scheme.Modules.pushforward p).mapCochainComplexPlus.obj
          (injectiveResolution M).cochainComplexPlus) ≫
      moduleSpecΓFunctor.rightDerivedFunctorPlus.map
        ((injectiveResolution M).rightDerivedFunctorPlusIso
          (Scheme.Modules.pushforward p)).hom := by
  let I := injectiveResolution M
  apply (cancel_mono (moduleSpecΓFunctor.rightDerivedFunctorPlus.map
    ((Scheme.Modules.pushforward p).rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map I.ιPlus)))).mp
  have hn := (nativeSectionsCompIso p).hom.naturality (DerivedCategory.Plus.Q.map I.ιPlus)
  simp only [Functor.comp_map] at hn
  erw [Category.assoc, ← hn,
    ← Category.assoc, InjectiveResolution.rightDerivedFunctorPlusIso_hom_comp,
    nativeSectionsCompIso_unit]
  simp only [Category.assoc]
  rw [← Functor.map_comp, InjectiveResolution.rightDerivedFunctorPlusIso_hom_comp]

private theorem cochainCounitMate (K : CochainComplex (Spec A).Modules ℤ)
    {L : CochainComplex (Spec A).Modules ℤ} (b : K ⟶ L) :
    ((tilde.adjunction (R := A)).mapHomologicalComplex (.up ℤ)).homEquiv
        ((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).obj K) L
        (Scheme.Modules.Complex.tildeGlobalSectionsCounit A (.up ℤ) K ≫ b) =
      (moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).map b := by
  rw [Scheme.Modules.Complex.tildeGlobalSectionsCounit_eq_nativeCounit,
    Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc,
    Adjunction.right_triangle_components, Category.id_comp]

private theorem affineHomEquivZero_chain (N : (Spec A).Modules) [N.IsQuasicoherent]
    (k : ℤ)
    (b : ((Scheme.Modules.pushforward p).mapHomologicalComplex (.up ℤ)).obj
        (injectiveResolution M).cochainComplex ⟶ (injectiveResolution N).cochainComplex⟦k⟧) :
    affineHomEquivZero p M N k
      ((CategoryTheory.Adjunction.rightDerivedResolutionIso
          (G := Scheme.Modules.pushforward p) (injectiveResolution M)).inv ≫
        DerivedCategory.Q.map b ≫
        (CategoryTheory.Adjunction.resolutionShiftIso (injectiveResolution N) k).inv) =
      (sourceSectionsModelIso p M).inv ≫
        DerivedCategory.Q.map
          (moduleSpecPushforwardGlobalSectionsComplexIso p (.up ℤ)
            (injectiveResolution M).cochainComplex).inv ≫
        DerivedCategory.Q.map ((moduleSpecΓFunctor.mapHomologicalComplex (.up ℤ)).map b) ≫
        (CategoryTheory.Adjunction.rightDerivedResolutionShiftIso
          (G := moduleSpecΓFunctor) (injectiveResolution N) k).hom ≫
        (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) k).map
          (DerivedCategory.Plus.ι.map (affineCoefficientIso N).hom) := by
  rw [affineHomEquivZero_apply, affineModelIso_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
    Category.comp_id, ← Functor.map_comp]
  rw [CategoryTheory.Adjunction.cochainDerivedHomEquivOfInjectiveResolution_map]
  rw [← Category.assoc,
    ((tilde.adjunction (R := A)).mapHomologicalComplex (.up ℤ)).homEquiv_naturality_left]
  rw [cochainCounitMate, Functor.map_comp]
  simp only [Category.assoc]

private def liftShiftedArrow (N : (Spec A).Modules) (k : ℤ)
    (a : DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedPushforwardPlus p).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) ⟶
      ((DerivedCategory.singleFunctor (Spec A).Modules 0).obj N)⟦k⟧) :
    ShiftedHom ((Scheme.Modules.derivedPushforwardPlus p).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M))
      ((DerivedCategory.Plus.singleFunctor (Spec A).Modules 0).obj N) k :=
  DerivedCategory.Plus.ι.preimage
    (a ≫ (DerivedCategory.Plus.ι.commShiftIso k).inv.app
      ((DerivedCategory.Plus.singleFunctor (Spec A).Modules 0).obj N))

omit [QuasiCompact p] [QuasiSeparated p] [M.IsQuasicoherent] in
private theorem liftShiftedArrow_map (N : (Spec A).Modules) (k : ℤ)
    (a : DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedPushforwardPlus p).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) ⟶
      ((DerivedCategory.singleFunctor (Spec A).Modules 0).obj N)⟦k⟧) :
    (liftShiftedArrow p M N k a).map DerivedCategory.Plus.ι = a := by
  rw [ShiftedHom.map, liftShiftedArrow, Functor.map_preimage, Category.assoc,
    Iso.inv_hom_id_app]
  exact Category.comp_id _

private theorem affineHomEquivZero_original (N : (Spec A).Modules) [N.IsQuasicoherent]
    (k : ℤ)
    (a : DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedPushforwardPlus p).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) ⟶
      ((DerivedCategory.singleFunctor (Spec A).Modules 0).obj N)⟦k⟧) :
    affineHomEquivZero p M N k a =
      DerivedCategory.Plus.ι.map ((nativeSectionsCompIso p).hom.app
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) ≫
      (liftShiftedArrow p M N k a).map
        (moduleSpecΓFunctor.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) ≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) k).map
        (DerivedCategory.Plus.ι.map (affineCoefficientIso N).hom) := by
  let I := injectiveResolution M
  let J := injectiveResolution N
  let L := J.cochainComplex⟦k⟧
  let : L.IsStrictlyGE (-k) := J.cochainComplex.isStrictlyGE_shift 0 k (-k) (by omega)
  let : ∀ i : ℤ, Injective (L.X i) := fun i => by
    change Injective (J.cochainComplex.X (i + k)); infer_instance
  let : L.IsKInjective := CochainComplex.isKInjective_of_injective L (-k)
  let e := CategoryTheory.Adjunction.rightDerivedResolutionIso
    (G := Scheme.Modules.pushforward p) I
  let s := CategoryTheory.Adjunction.resolutionShiftIso J k
  obtain ⟨b, hb⟩ := derived_map_surjective
    (((Scheme.Modules.pushforward p).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex)
    L (e.hom ≫ a ≫ s.hom)
  change DerivedCategory.Q.map b = e.hom ≫ a ≫ s.hom at hb
  have ha : a = e.inv ≫ DerivedCategory.Q.map b ≫ s.inv := by
    have h := congrArg (fun f => e.inv ≫ f ≫ s.inv) hb
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
      Category.comp_id] using h.symm
  rw [ha, affineHomEquivZero_chain]
  let B : ShiftedHom
      ((Scheme.Modules.pushforward p).mapCochainComplexPlus.obj I.cochainComplexPlus)
      J.cochainComplexPlus k := ObjectProperty.homMk
        (b ≫ ((CochainComplex.Plus.ι (Spec A).Modules).commShiftIso k).inv.app
          J.cochainComplexPlus)
  have hB : B.map (CochainComplex.Plus.ι (Spec A).Modules) = b := by
    change (b ≫ ((CochainComplex.Plus.ι (Spec A).Modules).commShiftIso k).inv.app
      J.cochainComplexPlus) ≫
        ((CochainComplex.Plus.ι (Spec A).Modules).commShiftIso k).hom.app
          J.cochainComplexPlus = b
    rw [Category.assoc, Iso.inv_hom_id_app]
    exact Category.comp_id _
  let i := asIso (DerivedCategory.Plus.Q.map J.ιPlus)
  have hl : liftShiftedArrow p M N k (e.inv ≫ DerivedCategory.Q.map b ≫ s.inv) =
      (I.rightDerivedFunctorPlusIso (Scheme.Modules.pushforward p)).inv ≫
        B.map DerivedCategory.Plus.Q ≫ i.inv⟦k⟧' := by
    apply (show Function.Injective (fun x => x.map DerivedCategory.Plus.ι) from by
      intro x y h; apply DerivedCategory.Plus.ι.map_injective
      simpa only [ShiftedHom.map, cancel_mono] using h)
    dsimp only
    erw [liftShiftedArrow_map, shifted_map_pre_post]
    have hq := shifted_map_iso (DerivedCategory.Plus.QCompιIso (Spec A).Modules) B
    simp only [ShiftedHom.comp_map] at hq
    rw [hq, hB]
    have hi : (DerivedCategory.Plus.QCompιIso (Spec A).Modules).inv.app
          J.cochainComplexPlus ≫ DerivedCategory.Plus.ι.map i.inv =
        inv (DerivedCategory.Q.map J.ι') := by
      apply (cancel_epi (DerivedCategory.Q.map J.ι')).mp
      have hn := (DerivedCategory.Plus.QCompιIso (Spec A).Modules).inv.naturality J.ιPlus
      change DerivedCategory.Q.map J.ι' ≫
          (DerivedCategory.Plus.QCompιIso (Spec A).Modules).inv.app J.cochainComplexPlus =
        (DerivedCategory.Plus.QCompιIso (Spec A).Modules).inv.app
          ((CochainComplex.singleFunctorPlus (Spec A).Modules 0).obj N) ≫
          DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map J.ιPlus) at hn
      have hi0 : DerivedCategory.Plus.Q.map J.ιPlus ≫ i.inv = 𝟙 _ := i.hom_inv_id
      rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp,
        hi0, CategoryTheory.Functor.map_id]
      erw [Category.comp_id, IsIso.hom_inv_id]
      rfl
    simp only [e, s, CategoryTheory.Adjunction.rightDerivedResolutionIso,
      CategoryTheory.Adjunction.resolutionShiftIso, Iso.trans_inv,
      Functor.mapIso_inv, Iso.symm_inv, Iso.app_inv,
      ShiftedHom.map, Category.assoc]
    rw [← Functor.map_comp, hi]
    rfl
  rw [hl, shifted_map_pre_post]
  have hu := ShiftedHom.map_naturality B moduleSpecΓFunctor.rightDerivedFunctorPlusUnit
  simp only [ShiftedHom.comp_map, ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp] at hu
  let r := I.rightDerivedFunctorPlusIso (Scheme.Modules.pushforward p)
  let g := I.rightDerivedFunctorPlusIso (sourceSections p)
  let c := moduleResolutionPushforwardSectionsPlusIso p I
  have hSource : (nativeSectionsCompIso p).hom.app
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) ≫
      moduleSpecΓFunctor.rightDerivedFunctorPlus.map r.inv =
    g.inv ≫ DerivedCategory.Plus.Q.map c.inv ≫
      moduleSpecΓFunctor.rightDerivedFunctorPlusUnit.app
        ((Scheme.Modules.pushforward p).mapCochainComplexPlus.obj I.cochainComplexPlus) := by
    have h := congrArg (fun z => g.inv ≫ z ≫
      moduleSpecΓFunctor.rightDerivedFunctorPlus.map r.inv) (sourceSectionsModel_comp p M)
    simp only [Category.assoc] at h
    change g.inv ≫ g.hom ≫ (nativeSectionsCompIso p).hom.app
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) ≫
        moduleSpecΓFunctor.rightDerivedFunctorPlus.map r.inv =
      g.inv ≫ DerivedCategory.Plus.Q.map c.inv ≫
        moduleSpecΓFunctor.rightDerivedFunctorPlusUnit.app
          ((Scheme.Modules.pushforward p).mapCochainComplexPlus.obj I.cochainComplexPlus) ≫
        moduleSpecΓFunctor.rightDerivedFunctorPlus.map r.hom ≫
          moduleSpecΓFunctor.rightDerivedFunctorPlus.map r.inv at h
    have hr : moduleSpecΓFunctor.rightDerivedFunctorPlus.map r.hom ≫
        moduleSpecΓFunctor.rightDerivedFunctorPlus.map r.inv = 𝟙 _ :=
      (moduleSpecΓFunctor.rightDerivedFunctorPlus.mapIso r).hom_inv_id
    rw [hr] at h
    erw [Category.comp_id, Iso.inv_hom_id_assoc] at h
    exact h
  have ht : moduleSpecΓFunctor.rightDerivedFunctorPlusUnit.app J.cochainComplexPlus ≫
      moduleSpecΓFunctor.rightDerivedFunctorPlus.map i.inv =
      (J.rightDerivedFunctorPlusIso moduleSpecΓFunctor).hom := by
    rw [InjectiveResolution.rightDerivedFunctorPlusIso_hom]
    dsimp only [i, asIso_inv]
    rw [Functor.map_inv]
  have hPlus : (nativeSectionsCompIso p).hom.app
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) ≫
      (show ShiftedHom _ _ k from r.inv ≫ B.map DerivedCategory.Plus.Q ≫ i.inv⟦k⟧').map
        moduleSpecΓFunctor.rightDerivedFunctorPlus ≫
      (affineCoefficientIso N).hom⟦k⟧' =
    (g.inv ≫ DerivedCategory.Plus.Q.map c.inv) ≫
      B.map (moduleSpecΓFunctor.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q) ≫
      ((J.rightDerivedFunctorPlusIso moduleSpecΓFunctor).hom ≫
        (affineCoefficientIso N).hom)⟦k⟧' := by
    rw [shifted_map_pre_post]
    simp only [Category.assoc]
    rw [reassoc_of% hSource, ← reassoc_of% hu]
    simp only [ShiftedHom.comp_map]
    rw [← (shiftFunctor (DerivedCategory.Plus (ModuleCat.{u} A)) k).map_comp,
      ← (shiftFunctor (DerivedCategory.Plus (ModuleCat.{u} A)) k).map_comp]
    erw [reassoc_of% ht]
  have hFull := congrArg (fun (z : ShiftedHom
      ((sourceSections p).rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M))
      ((DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0).obj
        (moduleSpecΓFunctor.obj N)) k) => z.map DerivedCategory.Plus.ι) hPlus
  simp only [shifted_map_pre_post, ShiftedHom.comp_map] at hFull
  have hRes := resolutionShiftSections J
    ((Scheme.Modules.pushforward p).mapCochainComplexPlus.obj I.cochainComplexPlus) k B
  rw [hB] at hRes
  rw [reassoc_of% hRes]
  have hc := (DerivedCategory.Plus.QCompιIso (ModuleCat.{u} A)).inv.naturality c.inv
  change DerivedCategory.Q.map c.inv.hom ≫
      (DerivedCategory.Plus.QCompιIso (ModuleCat.{u} A)).inv.app
        (moduleSpecΓFunctor.mapCochainComplexPlus.obj
          ((Scheme.Modules.pushforward p).mapCochainComplexPlus.obj I.cochainComplexPlus)) =
    (DerivedCategory.Plus.QCompιIso (ModuleCat.{u} A)).inv.app (sourceModel p M) ≫
      DerivedCategory.Plus.ι.map (DerivedCategory.Plus.Q.map c.inv) at hc
  have hfront : (sourceSectionsModelIso p M).inv ≫
      DerivedCategory.Q.map
        (moduleSpecPushforwardGlobalSectionsComplexIso p (.up ℤ) I.cochainComplex).inv ≫
      (DerivedCategory.Plus.QCompιIso (ModuleCat.{u} A)).inv.app
        (moduleSpecΓFunctor.mapCochainComplexPlus.obj
          ((Scheme.Modules.pushforward p).mapCochainComplexPlus.obj I.cochainComplexPlus)) =
    DerivedCategory.Plus.ι.map (g.inv ≫ DerivedCategory.Plus.Q.map c.inv) := by
    change (sourceSectionsModelIso p M).inv ≫
      (DerivedCategory.Q.map c.inv.hom ≫
        (DerivedCategory.Plus.QCompιIso (ModuleCat.{u} A)).inv.app
          (moduleSpecΓFunctor.mapCochainComplexPlus.obj
            ((Scheme.Modules.pushforward p).mapCochainComplexPlus.obj I.cochainComplexPlus))) = _
    rw [hc]
    simp only [sourceSectionsModelIso, CategoryTheory.Adjunction.rightDerivedResolutionIso,
      Iso.trans_inv, Iso.app_inv, Iso.symm_inv, Functor.mapIso_inv,
      Category.assoc, Functor.map_comp]
    rfl
  simp only [Category.assoc]
  erw [reassoc_of% hfront]
  simpa only [r, Functor.map_comp, Functor.comp_map, ShiftedHom.comp_map,
    Category.assoc] using hFull.symm

end Affine

/-- Actual affine-target derived Hom, for arbitrary quasicoherent target coefficient.
The original source resolution, affine direct-image model and pointwise adjunction
supply the inverse; no injectivity or quasicoherence of pushed resolution terms is assumed. -/
@[no_expose] def moduleSpecDerivedPushforwardHomAddEquiv
    {A : CommRingCat.{u}} {X : Scheme.{u}}
    (p : X ⟶ Spec A) [QuasiCompact p] [QuasiSeparated p]
    (M : X.Modules) [M.IsQuasicoherent] (N : (Spec A).Modules) [N.IsQuasicoherent]
    (n q : ℕ) :
    (DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedPushforwardPlus p).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) ⟶
      ((DerivedCategory.singleFunctor (Spec A).Modules (n : ℤ)).obj N)⟦(q : ℤ)⟧) ≃+
    (((moduleGlobalSectionsFunctorOfHom X
        (p.appTop.hom.comp (Scheme.ΓSpecIso A).inv.hom)).rightDerivedFunctorPlus ⋙
      DerivedCategory.Plus.ι).obj ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) ⟶
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) (n : ℤ)).obj
        (moduleSpecΓFunctor.obj N))⟦(q : ℤ)⟧) :=
  (homIsoAddEquiv (Iso.refl _) (coefficientShiftIso N n q)).trans
    ((affineHomEquivZero p M N ((q : ℤ) - n)).trans
      (homIsoAddEquiv (Iso.refl _)
        (coefficientShiftIso (moduleSpecΓFunctor.obj N) n q).symm))

/-- On every original shifted derived arrow, the equivalence is actual derived sections,
through the original global-sections composition and native coefficient and shift maps. -/
theorem moduleSpecDerivedPushforwardHomAddEquiv_apply
    {A : CommRingCat.{u}} {X : Scheme.{u}}
    (p : X ⟶ Spec A) [QuasiCompact p] [QuasiSeparated p]
    (M : X.Modules) [M.IsQuasicoherent] (N : (Spec A).Modules) [N.IsQuasicoherent]
    (n q : ℕ)
    (a : DerivedCategory.Plus.ι.obj ((Scheme.Modules.derivedPushforwardPlus p).obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) ⟶
      ((DerivedCategory.singleFunctor (Spec A).Modules (n : ℤ)).obj N)⟦(q : ℤ)⟧) :
    let k := (q : ℤ) - n
    let c := ((DerivedCategory.singleFunctors (Spec A).Modules).shiftIso
         (q : ℤ) ((n : ℤ) - q) n (by omega)).app N ≪≫
      (((DerivedCategory.singleFunctors (Spec A).Modules).shiftIso
         k ((n : ℤ) - q) 0 (by omega)).app N).symm
    let d := ((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso
         (q : ℤ) ((n : ℤ) - q) n (by omega)).app (moduleSpecΓFunctor.obj N) ≪≫
      (((DerivedCategory.singleFunctors (ModuleCat.{u} A)).shiftIso
         k ((n : ℤ) - q) 0 (by omega)).app (moduleSpecΓFunctor.obj N)).symm
    let v : ShiftedHom
        ((Scheme.Modules.derivedPushforwardPlus p).obj
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M))
        ((DerivedCategory.Plus.singleFunctor (Spec A).Modules 0).obj N) k :=
      DerivedCategory.Plus.ι.preimage
        ((a ≫ c.hom) ≫ (DerivedCategory.Plus.ι.commShiftIso k).inv.app
          ((DerivedCategory.Plus.singleFunctor (Spec A).Modules 0).obj N))
    let e : moduleGlobalSectionsFunctorOfHom (Spec A) (Scheme.ΓSpecIso A).inv.hom ≅
        moduleSpecΓFunctor :=
      NatIso.ofComponents
        (fun L => (moduleTopSectionsIso (Spec A) (Scheme.ΓSpecIso A).inv.hom L).symm)
        (by intro L L' f; ext x; rfl)
    let C := moduleDerivedGlobalSectionsPushforwardCompIso p (Scheme.ΓSpecIso A).inv.hom ≪≫
      isoWhiskerLeft (Scheme.Modules.pushforward p).rightDerivedFunctorPlus
        ((moduleGlobalSectionsFunctorOfHom (Spec A)
          (Scheme.ΓSpecIso A).inv.hom).rightDerivedFunctorPlusIso
           e)
    let E := moduleSpecΓFunctor.rightDerivedFunctorPlusSingleIsoOfAcyclic N
      (AffineDerived.isZero_rightDerived_globalSections_succ N)
    moduleSpecDerivedPushforwardHomAddEquiv p M N n q a =
      DerivedCategory.Plus.ι.map (C.hom.app
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M)) ≫
      v.map (moduleSpecΓFunctor.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) ≫
      (shiftFunctor (DerivedCategory (ModuleCat.{u} A)) k).map
        (DerivedCategory.Plus.ι.map E.hom) ≫ d.inv := by
  dsimp only
  change (𝟙 _ ≫ affineHomEquivZero p M N ((q : ℤ) - n)
    (𝟙 _ ≫ a ≫ (coefficientShiftIso N n q).hom) ≫
      (coefficientShiftIso (moduleSpecΓFunctor.obj N) n q).inv) = _
  rw [Category.id_comp, Category.id_comp, affineHomEquivZero_original]
  simp only [nativeSectionsCompIso, specStructuralSectionsIso, liftShiftedArrow,
    affineCoefficientIso, coefficientShiftIso, Category.assoc]

end AlgebraicGeometry.Scheme.Cohomology
