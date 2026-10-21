/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology.Coherence

/-!
# The unit square for degree-zero flat base change

The actual higher-direct-image base-change map in degree zero commutes with
the original transformations to the zeroth right-derived functors. The proof
uses the installed derived unit, its injective-resolution augmentation, and
the existing exact-single and homology comparisons. Flatness of the base
arrow is the only geometric hypothesis.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- Fix the standard derived-category universe for the module-sheaf comparison. -/
local instance degreeZeroBaseChangeStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

section Single

variable {X Y Z : Scheme.{u}} (F : X.Modules ⥤ Y.Modules) [F.Additive]

private def singleComplexIso (M : X.Modules) :
    F.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus X.Modules 0).obj M) ≅
      (CochainComplex.singleFunctorPlus Y.Modules 0).obj (F.obj M) :=
  (CochainComplex.plus Y.Modules).isoMk
    ((singleMapHomologicalComplex F (.up ℤ) 0).app M)

private theorem singleComplexIso_comp (G : Y.Modules ⥤ Z.Modules) [G.Additive]
    (M : X.Modules) :
    (singleComplexIso (F ⋙ G) M).hom =
      G.mapCochainComplexPlus.map (singleComplexIso F M).hom ≫
        (singleComplexIso G (F.obj M)).hom := by
  apply ObjectProperty.hom_ext
  change (singleMapHomologicalComplex (F ⋙ G) (.up ℤ) 0).hom.app M =
    (G.mapHomologicalComplex (.up ℤ)).map
        ((singleMapHomologicalComplex F (.up ℤ) 0).hom.app M) ≫
      (singleMapHomologicalComplex G (.up ℤ) 0).hom.app (F.obj M)
  simpa only [Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
    Iso.refl_inv, NatTrans.mapHomologicalComplex_id, NatTrans.id_app, Category.id_comp] using
    singleMapHomologicalComplex_comp_hom_app F G (.up ℤ) (0 : ℤ) M

private theorem singleComplexIso_naturality {G : X.Modules ⥤ Y.Modules} [G.Additive]
    (τ : F ⟶ G) (M : X.Modules) :
    (NatTrans.mapCochainComplexPlus τ).app
          ((CochainComplex.singleFunctorPlus X.Modules 0).obj M) ≫
        (singleComplexIso G M).hom =
      (singleComplexIso F M).hom ≫
        (CochainComplex.singleFunctorPlus Y.Modules 0).map (τ.app M) := by
  apply ObjectProperty.hom_ext
  change (τ.mapHomologicalComplex (.up ℤ)).app
        ((single X.Modules (.up ℤ) 0).obj M) ≫
      (singleMapHomologicalComplex G (.up ℤ) 0).hom.app M =
    (singleMapHomologicalComplex F (.up ℤ) 0).hom.app M ≫
      (single Y.Modules (.up ℤ) 0).map (τ.app M)
  rw [natTransMapHomologicalComplex_app_single_obj]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

private def singleDerivedUnit (M : X.Modules) :
    (DerivedCategory.Plus.singleFunctor Y.Modules 0).obj (F.obj M) ⟶
      F.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) :=
  DerivedCategory.Plus.Q.map (singleComplexIso F M).inv ≫
    F.rightDerivedFunctorPlusUnit.app ((CochainComplex.singleFunctorPlus X.Modules 0).obj M)

private theorem singleDerivedUnit_eq_inv [F.PreservesHomology] (M : X.Modules) :
    singleDerivedUnit F M = (F.rightDerivedFunctorPlusSingleIso 0).inv.app M := by
  apply (cancel_mono ((F.rightDerivedFunctorPlusSingleIso 0).hom.app M)).mp
  rw [singleDerivedUnit, Category.assoc, F.rightDerivedFunctorPlusSingleIso_unit]
  change DerivedCategory.Plus.Q.map (singleComplexIso F M).inv ≫
      DerivedCategory.Plus.Q.map (singleComplexIso F M).hom = _
  rw [← Functor.map_comp, Iso.inv_hom_id]
  simp only [CategoryTheory.Functor.map_id, Iso.inv_hom_id_app]
  rfl

private theorem compositeSingleUnit (G : Y.Modules ⥤ Z.Modules) [G.Additive]
    (M : X.Modules) :
    DerivedCategory.Plus.Q.map (singleComplexIso (F ⋙ G) M).hom ≫
        singleDerivedUnit G (F.obj M) ≫
        G.rightDerivedFunctorPlus.map (singleDerivedUnit F M) =
      (Functor.rightDerivedFunctorPlusCompUnit F G).app
        ((CochainComplex.singleFunctorPlus X.Modules 0).obj M) := by
  let K := (CochainComplex.singleFunctorPlus X.Modules 0).obj M
  let sF := singleComplexIso F M
  let sG := singleComplexIso G (F.obj M)
  have hn := G.rightDerivedFunctorPlusUnit.naturality sF.hom
  change DerivedCategory.Plus.Q.map (G.mapCochainComplexPlus.map sF.hom) ≫
      G.rightDerivedFunctorPlusUnit.app
        ((CochainComplex.singleFunctorPlus Y.Modules 0).obj (F.obj M)) =
    G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) ≫
      G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map sF.hom) at hn
  rw [singleComplexIso_comp, Functor.map_comp, singleDerivedUnit, singleDerivedUnit,
    Functor.map_comp, Functor.rightDerivedFunctorPlusCompUnit_app]
  simp only [Category.assoc]
  have hG : DerivedCategory.Plus.Q.map sG.hom ≫
      DerivedCategory.Plus.Q.map sG.inv = 𝟙 _ :=
    (DerivedCategory.Plus.Q.mapIso sG).hom_inv_id
  have hF : G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map sF.hom) ≫
      G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map sF.inv) = 𝟙 _ :=
    (G.rightDerivedFunctorPlus.mapIso (DerivedCategory.Plus.Q.mapIso sF)).hom_inv_id
  erw [reassoc_of% hG, reassoc_of% hn, reassoc_of% hF]

private def mappedSingleCyclesIso (M : X.Modules) :
    (((F.mapHomologicalComplex (.up ℤ)).obj
      ((single X.Modules (.up ℤ) 0).obj M)).cycles 0) ≅ F.obj M :=
  (cyclesFunctor Y.Modules (.up ℤ) 0).mapIso
      ((singleMapHomologicalComplex F (.up ℤ) 0).app M) ≪≫
    singleObjCyclesSelfIso (.up ℤ) 0 (F.obj M)

private theorem mappedSingleCyclesIso_inv_iCycles (M : X.Modules) :
    (mappedSingleCyclesIso F M).inv ≫
      (((F.mapHomologicalComplex (.up ℤ)).obj
        ((single X.Modules (.up ℤ) 0).obj M)).iCycles 0) =
      F.map (singleObjXSelf (.up ℤ) 0 M).inv := by
  change ((singleObjCyclesSelfIso (.up ℤ) 0 (F.obj M)).inv ≫
      cyclesMap ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) 0) ≫
      ((F.mapHomologicalComplex (.up ℤ)).obj
        ((single X.Modules (.up ℤ) 0).obj M)).iCycles 0 = _
  rw [Category.assoc]
  erw [cyclesMap_i, ← Category.assoc, singleObjCyclesSelfIso_inv_iCycles]
  simp only [singleMapHomologicalComplex_inv_app_self,
    Iso.inv_hom_id_assoc]

private def mappedSingleHomologyIso (M : X.Modules) :
    (((F.mapHomologicalComplex (.up ℤ)).obj
      ((single X.Modules (.up ℤ) 0).obj M)).homology 0) ≅ F.obj M :=
  (homologyFunctor Y.Modules (.up ℤ) 0).mapIso
      ((singleMapHomologicalComplex F (.up ℤ) 0).app M) ≪≫
    singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)

private theorem mappedSingleCyclesIso_inv_homologyπ (M : X.Modules) :
    (mappedSingleCyclesIso F M).inv ≫
      (((F.mapHomologicalComplex (.up ℤ)).obj
        ((single X.Modules (.up ℤ) 0).obj M)).homologyπ 0) =
      (mappedSingleHomologyIso F M).inv := by
  change ((singleObjCyclesSelfIso (.up ℤ) 0 (F.obj M)).inv ≫
      cyclesMap ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) 0) ≫
      ((F.mapHomologicalComplex (.up ℤ)).obj
        ((single X.Modules (.up ℤ) 0).obj M)).homologyπ 0 =
    (singleObjHomologySelfIso (.up ℤ) 0 (F.obj M)).inv ≫
      homologyMap ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app M) 0
  rw [Category.assoc]
  erw [← homologyπ_naturality,
    ← Category.assoc, singleObjCyclesSelfIso_inv_homologyπ]

private theorem mappedSingleHomologyIso_inv_resolution (M : X.Modules)
    (I : InjectiveResolution M) :
    (mappedSingleHomologyIso F M).inv ≫
      homologyMap ((F.mapHomologicalComplex (.up ℤ)).map I.ι') 0 =
    I.toRightDerivedZeroCochainCycles F ≫
      (((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).homologyπ 0) := by
  have hc :
      (mappedSingleCyclesIso F M).inv ≫
        cyclesMap ((F.mapHomologicalComplex (.up ℤ)).map I.ι') 0 =
      I.toRightDerivedZeroCochainCycles F := by
    apply (cancel_mono
      (((F.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex).iCycles 0)).mp
    rw [Category.assoc, cyclesMap_i, ← Category.assoc,
      mappedSingleCyclesIso_inv_iCycles,
      InjectiveResolution.toRightDerivedZeroCochainCycles_comp_iCycles]
    change F.map (singleObjXSelf (.up ℤ) 0 M).inv ≫ F.map (I.ι'.f 0) = _
    rw [I.ι'_f_zero, Functor.map_comp, Functor.map_comp,
      ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← mappedSingleCyclesIso_inv_homologyπ, Category.assoc,
    homologyπ_naturality, ← Category.assoc, hc]

private def mappedSingleDerivedHomologyIso (M : X.Modules) :
    (DerivedCategory.Plus.homologyFunctor Y.Modules 0).obj
      (DerivedCategory.Plus.Q.obj
        (F.mapCochainComplexPlus.obj
          ((CochainComplex.singleFunctorPlus X.Modules 0).obj M))) ≅ F.obj M :=
  (DerivedCategory.Plus.homologyFunctorFactors (A := Y.Modules) 0).app
      (F.mapCochainComplexPlus.obj
        ((CochainComplex.singleFunctorPlus X.Modules 0).obj M)) ≪≫
    mappedSingleHomologyIso F M

private theorem toRightDerivedZero_comp_singleHomology_unit (M : X.Modules) :
    F.toRightDerivedZero.app M ≫ (F.rightDerivedSingleHomologyIso 0).hom.app M =
      (mappedSingleDerivedHomologyIso F M).inv ≫
        (DerivedCategory.Plus.homologyFunctor Y.Modules 0).map
          (F.rightDerivedFunctorPlusUnit.app
            ((CochainComplex.singleFunctorPlus X.Modules 0).obj M)) := by
  let I := injectiveResolution M
  rw [F.rightDerivedSingleHomologyIso_hom_app I,
    InjectiveResolution.isoRightDerivedSingleHomology_hom,
    ← Category.assoc, InjectiveResolution.toRightDerivedZero_comp_isoRightDerivedObjCochain,
    ← mappedSingleHomologyIso_inv_resolution F M I]
  have hn := (DerivedCategory.Plus.homologyFunctorFactors (A := Y.Modules) 0).inv.naturality
    (F.mapCochainComplexPlus.map I.ιPlus)
  change homologyMap ((F.mapHomologicalComplex (.up ℤ)).map I.ι') 0 ≫
      (DerivedCategory.Plus.homologyFunctorFactors (A := Y.Modules) 0).inv.app
        (F.mapCochainComplexPlus.obj I.cochainComplexPlus) =
    (DerivedCategory.Plus.homologyFunctorFactors (A := Y.Modules) 0).inv.app
      (F.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus X.Modules 0).obj M)) ≫
        (DerivedCategory.Plus.homologyFunctor Y.Modules 0).map
          (DerivedCategory.Plus.Q.map (F.mapCochainComplexPlus.map I.ιPlus)) at hn
  simp only [Category.assoc]
  erw [reassoc_of% hn, ← Functor.map_comp, I.rightDerivedFunctorPlusIso_unit F]
  exact (Category.assoc _ _ _).symm

private theorem singleHomology_comparison (Y : Scheme.{u}) (M : Y.Modules) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso Y.Modules 0).hom.app M =
      (DerivedCategory.Plus.homologyFunctorFactors (A := Y.Modules) 0).hom.app
        ((CochainComplex.singleFunctorPlus Y.Modules 0).obj M) ≫
      (singleObjHomologySelfIso (.up ℤ) 0 M).hom := by
  dsimp [DerivedCategory.singleFunctorCompHomologyFunctorIso,
    DerivedCategory.Plus.homologyFunctorFactors,
    DerivedCategory.singleFunctorsPostcompQIso, DerivedCategory.Plus.QCompιIso,
    ObjectProperty.liftCompιIso]
  let Z := (single Y.Modules (.up ℤ) 0).obj M
  let V := DerivedCategory.Q.obj Z
  let H := DerivedCategory.homologyFunctor Y.Modules 0
  let h := (DerivedCategory.homologyFunctorFactors Y.Modules 0).hom.app Z
  let e := (singleObjHomologySelfIso (.up ℤ) 0 M).hom
  change H.map (𝟙 V) ≫ 𝟙 (H.obj V) ≫ h ≫ e =
    (𝟙 (H.obj V) ≫ H.map (𝟙 V) ≫ 𝟙 (H.obj V) ≫ h) ≫ e
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]

private theorem mappedSingleDerivedHomologyIso_eq (M : X.Modules) :
    mappedSingleDerivedHomologyIso F M =
      (DerivedCategory.Plus.homologyFunctor Y.Modules 0).mapIso
        (DerivedCategory.Plus.Q.mapIso (singleComplexIso F M)) ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso Y.Modules 0).app (F.obj M) := by
  apply Iso.ext
  rw [Iso.trans_hom, Functor.mapIso_hom, Functor.mapIso_hom, Iso.app_hom,
    singleHomology_comparison, ← Category.assoc]
  have hn := (DerivedCategory.Plus.homologyFunctorFactors (A := Y.Modules) 0).hom.naturality
    (singleComplexIso F M).hom
  change (DerivedCategory.Plus.homologyFunctor Y.Modules 0).map
      (DerivedCategory.Plus.Q.map (singleComplexIso F M).hom) ≫
      (DerivedCategory.Plus.homologyFunctorFactors (A := Y.Modules) 0).hom.app
        ((CochainComplex.singleFunctorPlus Y.Modules 0).obj (F.obj M)) =
    (DerivedCategory.Plus.homologyFunctorFactors (A := Y.Modules) 0).hom.app
      (F.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus X.Modules 0).obj M)) ≫
      homologyMap (singleComplexIso F M).hom.hom 0 at hn
  rw [hn]
  exact (Category.assoc _ _ _).symm

private theorem toRightDerivedZero_single_unit (M : X.Modules) :
    F.toRightDerivedZero.app M ≫ (F.rightDerivedSingleHomologyIso 0).hom.app M =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso Y.Modules 0).inv.app (F.obj M) ≫
        (DerivedCategory.Plus.homologyFunctor Y.Modules 0).map (singleDerivedUnit F M) := by
  rw [toRightDerivedZero_comp_singleHomology_unit, mappedSingleDerivedHomologyIso_eq]
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, singleDerivedUnit,
    Functor.map_comp, Category.assoc]

private theorem exact_single_homology_inv [F.PreservesHomology] (M : X.Modules) :
    F.map ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).inv.app M) ≫
        (F.rightDerivedFunctorPlusHomologyIso 0).inv.app
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) =
      (DerivedCategory.singleFunctorCompHomologyFunctorIso Y.Modules 0).inv.app (F.obj M) ≫
        (DerivedCategory.Plus.homologyFunctor Y.Modules 0).map (singleDerivedUnit F M) := by
  have hh :
      (DerivedCategory.Plus.homologyFunctor Y.Modules 0).mapIso
          ((F.rightDerivedFunctorPlusSingleIso 0).app M) ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso Y.Modules 0).app (F.obj M) =
      (F.rightDerivedFunctorPlusHomologyIso 0).app
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) ≪≫
        F.mapIso ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules 0).app M) :=
    Iso.ext (F.rightDerivedFunctorPlusSingleIso_homology 0 M)
  have hi := congrArg Iso.inv hh
  simpa only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv,
    singleDerivedUnit_eq_inv] using hi.symm

end Single

section BaseChange

variable {W U V X : Scheme.{u}}
  (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (h : IsPullback a b f j) [Flat j]

private theorem derivedFlatBaseChangeMap_single_unit (M : U.Modules) :
    letI := flat_cartesian_baseChange a b f j h
    singleDerivedUnit (pullback j) ((pushforward f).obj M) ≫
        (pullback j).rightDerivedFunctorPlus.map (singleDerivedUnit (pushforward f) M) ≫
        (derivedFlatBaseChangeMap a b f j h).app
          ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M) ≫
        (pushforward b).rightDerivedFunctorPlus.map
          (((pullback a).rightDerivedFunctorPlusSingleIso 0).hom.app M) =
      (DerivedCategory.Plus.singleFunctor V.Modules 0).map
          ((cartesianBaseChangeMap a b f j h).app M) ≫
        singleDerivedUnit (pushforward b) ((pullback a).obj M) := by
  let := flat_cartesian_baseChange a b f j h
  let F := pushforward f
  let J := pullback j
  let A := pullback a
  let B := pushforward b
  let K := (CochainComplex.singleFunctorPlus U.Modules 0).obj M
  let c := cartesianBaseChangeMap a b f j h
  let δ := derivedFlatBaseChangeMap a b f j h
  let eA := A.rightDerivedFunctorPlusSingleIso 0
  have he := derivedFlatBaseChangeMap_unit a b f j h K
  have hn := congrArg (DerivedCategory.Plus.Q (C := V.Modules)).map
    (singleComplexIso_naturality (F ⋙ J) c M)
  simp only [Functor.map_comp] at hn
  change DerivedCategory.Plus.Q.map ((NatTrans.mapCochainComplexPlus c).app K) ≫
      DerivedCategory.Plus.Q.map (singleComplexIso (A ⋙ B) M).hom =
    DerivedCategory.Plus.Q.map (singleComplexIso (F ⋙ J) M).hom ≫
      (DerivedCategory.Plus.singleFunctor V.Modules 0).map (c.app M) at hn
  have hA := compositeSingleUnit A B M
  rw [singleDerivedUnit_eq_inv A M] at hA
  have hA' := congrArg (fun z => z ≫ B.rightDerivedFunctorPlus.map (eA.hom.app M)) hA
  simp only [eA, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app] at hA'
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hA'
  apply (cancel_epi (DerivedCategory.Plus.Q.map (singleComplexIso (F ⋙ J) M).hom)).mp
  change DerivedCategory.Plus.Q.map (singleComplexIso (F ⋙ J) M).hom ≫
      singleDerivedUnit J (F.obj M) ≫ J.rightDerivedFunctorPlus.map (singleDerivedUnit F M) ≫
      δ.app (DerivedCategory.Plus.Q.obj K) ≫ B.rightDerivedFunctorPlus.map (eA.hom.app M) =
    DerivedCategory.Plus.Q.map (singleComplexIso (F ⋙ J) M).hom ≫
      (DerivedCategory.Plus.singleFunctor V.Modules 0).map (c.app M) ≫
      singleDerivedUnit B (A.obj M)
  erw [reassoc_of% compositeSingleUnit F J M, reassoc_of% he,
    ← reassoc_of% hn, ← hA']

/-- Degree-zero flat base change commutes with the original maps to the zeroth
right-derived functors. The square retains the actual cartesian base-change
map, higher-direct-image map, coefficient, and original four scheme arrows. -/
theorem higherDirectImageFlatBaseChangeMap_zero_unit (M : U.Modules) :
    (pullback j).map ((pushforward f).toRightDerivedZero.app M) ≫
        (higherDirectImageFlatBaseChangeMap a b f j h 0).app M =
      (cartesianBaseChangeMap a b f j h).app M ≫
        (pushforward b).toRightDerivedZero.app ((pullback a).obj M) := by
  let := flat_cartesian_baseChange a b f j h
  let F := pushforward f
  let J := pullback j
  let A := pullback a
  let B := pushforward b
  let H := DerivedCategory.Plus.homologyFunctor V.Modules 0
  let eJ := J.rightDerivedFunctorPlusHomologyIso 0
  let c := (cartesianBaseChangeMap a b f j h).app M
  let δ := (derivedFlatBaseChangeMap a b f j h).app
    ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)
  let eA := (A.rightDerivedFunctorPlusSingleIso 0).hom.app M
  have hn := eJ.inv.naturality (singleDerivedUnit F M)
  change J.map ((DerivedCategory.Plus.homologyFunctor X.Modules 0).map
      (singleDerivedUnit F M)) ≫
        eJ.inv.app (F.rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) =
    eJ.inv.app ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj (F.obj M)) ≫
      H.map (J.rightDerivedFunctorPlus.map (singleDerivedUnit F M)) at hn
  have hs := congrArg H.map (derivedFlatBaseChangeMap_single_unit a b f j h M)
  simp only [Functor.map_comp] at hs
  have hc := (DerivedCategory.singleFunctorCompHomologyFunctorIso V.Modules 0).inv.naturality c
  change c ≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso V.Modules 0).inv.app
      (B.obj (A.obj M)) =
    (DerivedCategory.singleFunctorCompHomologyFunctorIso V.Modules 0).inv.app (J.obj (F.obj M)) ≫
      H.map ((DerivedCategory.Plus.singleFunctor V.Modules 0).map c) at hc
  apply (cancel_mono ((B.rightDerivedSingleHomologyIso 0).hom.app (A.obj M))).mp
  rw [higherDirectImageFlatBaseChangeMap_app]
  simp only [Category.assoc]
  change J.map (F.toRightDerivedZero.app M) ≫
      J.map ((F.rightDerivedSingleHomologyIso 0).hom.app M) ≫
      eJ.inv.app (F.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) ≫
      H.map δ ≫ H.map (B.rightDerivedFunctorPlus.map eA) ≫
      (B.rightDerivedSingleHomologyIso 0).inv.app (A.obj M) ≫
      (B.rightDerivedSingleHomologyIso 0).hom.app (A.obj M) =
    c ≫ B.toRightDerivedZero.app (A.obj M) ≫
      (B.rightDerivedSingleHomologyIso 0).hom.app (A.obj M)
  simp only [Iso.inv_hom_id_app]
  erw [Category.comp_id]
  rw [← J.map_comp_assoc, toRightDerivedZero_single_unit, J.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hn, ← Category.assoc,
    exact_single_homology_inv J (F.obj M)]
  simp only [Category.assoc]
  erw [hs, ← reassoc_of% hc, ← toRightDerivedZero_single_unit B (A.obj M)]

end BaseChange

end AlgebraicGeometry.Scheme.Modules
