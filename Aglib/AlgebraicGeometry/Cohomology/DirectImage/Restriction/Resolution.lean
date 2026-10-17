/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.DirectImage.Restriction
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.ExactResolution.Unit
public import Aglib.Algebra.Homology.CochainComplexPlus.NatTrans

/-!
# Original higher-image open restriction on supplied resolutions

The native higher-image open comparison is computed by the original
cartesian restriction map on a supplied module injective resolution and
the native comparison with a supplied target resolution. The original
installed derived units determine the map. This normalization applies to
all module coefficients, without quasicoherence or finiteness assumptions.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- All models use the installed standard derived categories of the actual module sheaves. -/
local instance openResolutionStandard (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b f j)
  (M : U.Modules) (I : InjectiveResolution M)
  (J : InjectiveResolution ((restrictFunctor a).obj M))

/-- The original cartesian open comparison on a supplied resolution, followed by native
pushforward of the original exact-restriction resolution comparison. -/
def openBaseChangeResolutionMapPlus :
    (pushforward f ⋙ restrictFunctor j).mapCochainComplexPlus.obj I.cochainComplexPlus ⟶
      (pushforward b).mapCochainComplexPlus.obj J.cochainComplexPlus :=
  (NatTrans.mapCochainComplexPlus (cartesianOpenBaseChange a b f j h).hom).app
      I.cochainComplexPlus ≫
    (pushforward b).mapCochainComplexPlus.map
      (InjectiveResolution.mapCochainComparisonPlus (restrictFunctor a) I J)

/-- Every component is the original ordinary cartesian mate and original chosen resolution
comparison component, with the actual geometric pushforward. -/
theorem openBaseChangeResolutionMapPlus_hom_f (i : ℤ) :
    (openBaseChangeResolutionMapPlus a b f j h M I J).hom.f i =
      ((cartesianOpenBaseChange a b f j h).hom).app (I.cochainComplex.X i) ≫
        (pushforward b).map
          ((InjectiveResolution.mapCochainComparison (restrictFunctor a) I J).f i) := rfl

/-- The original source model is the exact open-restriction unit followed by the original
right-derived resolution comparison for pushforward. -/
private def openBaseChangeResolutionSourceIso :
    DerivedCategory.Plus.Q.obj
        ((pushforward f ⋙ restrictFunctor j).mapCochainComplexPlus.obj I.cochainComplexPlus) ≅
      ((pushforward f).rightDerivedFunctorPlus ⋙ (restrictFunctor j).rightDerivedFunctorPlus).obj
        ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M) := by
  letI : IsIso (restrictFunctor j).rightDerivedFunctorPlusUnit :=
    (restrictFunctor j).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  exact asIso ((restrictFunctor j).rightDerivedFunctorPlusUnit.app
      ((pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus)) ≪≫
    (restrictFunctor j).rightDerivedFunctorPlus.mapIso
      (I.rightDerivedFunctorPlusIso (pushforward f))

/-- The original target model is the native pushforward resolution comparison and the inverse
native exact-restriction/single comparison. -/
private def openBaseChangeResolutionTargetIso :
    DerivedCategory.Plus.Q.obj ((pushforward b).mapCochainComplexPlus.obj J.cochainComplexPlus) ≅
      ((restrictFunctor a).rightDerivedFunctorPlus ⋙ (pushforward b).rightDerivedFunctorPlus).obj
        ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M) :=
  J.rightDerivedFunctorPlusIso (pushforward b) ≪≫
    (pushforward b).rightDerivedFunctorPlus.mapIso
      (((restrictFunctor a).rightDerivedFunctorPlusSingleIso 0).app M).symm

private theorem openRestrictionSingleIso_inv_map_resolution :
    ((restrictFunctor a).rightDerivedFunctorPlusSingleIso 0).inv.app M ≫
        (restrictFunctor a).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map I.ιPlus) =
      DerivedCategory.Plus.Q.map
          (InjectiveResolution.mapCochainAugmentationPlus (restrictFunctor a) I) ≫
        (restrictFunctor a).rightDerivedFunctorPlusUnit.app I.cochainComplexPlus := by
  let A := restrictFunctor a
  let e := A.rightDerivedFunctorPlusSingleIso 0
  let s : A.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus U.Modules 0).obj M) ≅
      (CochainComplex.singleFunctorPlus W.Modules 0).obj (A.obj M) :=
    (CochainComplex.plus W.Modules).isoMk
      ((HomologicalComplex.singleMapHomologicalComplex A (.up ℤ) 0).app M)
  have he : A.rightDerivedFunctorPlusUnit.app
        ((CochainComplex.singleFunctorPlus U.Modules 0).obj M) ≫ e.hom.app M =
      DerivedCategory.Plus.Q.map s.hom := A.rightDerivedFunctorPlusSingleIso_unit 0 M
  have hi : e.inv.app M = DerivedCategory.Plus.Q.map s.inv ≫
      A.rightDerivedFunctorPlusUnit.app
        ((CochainComplex.singleFunctorPlus U.Modules 0).obj M) := by
    apply (cancel_mono (e.hom.app M)).mp
    rw [Iso.inv_hom_id_app, Category.assoc, he, ← Functor.map_comp,
      s.inv_hom_id]
    exact ((DerivedCategory.Plus.Q (C := W.Modules)).map_id
      ((CochainComplex.singleFunctorPlus W.Modules 0).obj (A.obj M))).symm
  have hn := A.rightDerivedFunctorPlusUnit.naturality I.ιPlus
  change DerivedCategory.Plus.Q.map (A.mapCochainComplexPlus.map I.ιPlus) ≫
      A.rightDerivedFunctorPlusUnit.app I.cochainComplexPlus =
    A.rightDerivedFunctorPlusUnit.app
        ((CochainComplex.singleFunctorPlus U.Modules 0).obj M) ≫
      A.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map I.ιPlus) at hn
  change e.inv.app M ≫ A.rightDerivedFunctorPlus.map _ = _
  rw [hi, Category.assoc, ← hn, ← Category.assoc, ← Functor.map_comp]
  rfl

private theorem openBaseChangeResolutionSourceIso_hom_comp :
    (openBaseChangeResolutionSourceIso f j M I).hom ≫
        ((pushforward f).rightDerivedFunctorPlus ⋙
          (restrictFunctor j).rightDerivedFunctorPlus).map (DerivedCategory.Plus.Q.map I.ιPlus) =
      (Functor.rightDerivedFunctorPlusCompUnit (pushforward f) (restrictFunctor j)).app
        I.cochainComplexPlus := by
  simp only [openBaseChangeResolutionSourceIso, Iso.trans_hom, asIso_hom,
    Functor.mapIso_hom, Functor.comp_map, Category.assoc]
  rw [← Functor.map_comp, InjectiveResolution.rightDerivedFunctorPlusIso_hom_comp]
  exact ((pushforward f).rightDerivedFunctorPlusCompUnit_app (restrictFunctor j)
    I.cochainComplexPlus).symm

private theorem openBaseChangeResolutionTargetIso_hom_comp :
    (openBaseChangeResolutionTargetIso a b M J).hom ≫
        ((restrictFunctor a).rightDerivedFunctorPlus ⋙
          (pushforward b).rightDerivedFunctorPlus).map (DerivedCategory.Plus.Q.map I.ιPlus) =
      (J.rightDerivedFunctorPlusIso (pushforward b)).hom ≫
        (pushforward b).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map
            (InjectiveResolution.mapCochainAugmentationPlus (restrictFunctor a) I)) ≫
        (pushforward b).rightDerivedFunctorPlus.map
          ((restrictFunctor a).rightDerivedFunctorPlusUnit.app I.cochainComplexPlus) := by
  simp only [openBaseChangeResolutionTargetIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_inv, Functor.comp_map, Category.assoc]
  rw [← Functor.map_comp, openRestrictionSingleIso_inv_map_resolution,
    Functor.map_comp]

/-- The actual chain map represents the original installed derived open comparison on
the coefficient single, through its original source and target resolution comparisons. -/
private theorem openBaseChangeResolutionMapPlus_derived :
    DerivedCategory.Plus.Q.map (openBaseChangeResolutionMapPlus a b f j h M I J) ≫
        (openBaseChangeResolutionTargetIso a b M J).hom =
      (openBaseChangeResolutionSourceIso f j M I).hom ≫
        (derivedOpenBaseChangeIso a b f j h).hom.app
          ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M) := by
  let ν := ((restrictFunctor a).rightDerivedFunctorPlus ⋙
    (pushforward b).rightDerivedFunctorPlus).map (DerivedCategory.Plus.Q.map I.ιPlus)
  let : IsIso ν := by
    dsimp only [ν]
    infer_instance
  apply (cancel_mono ν).mp
  have hn := (derivedOpenBaseChangeIso a b f j h).hom.naturality
    (DerivedCategory.Plus.Q.map I.ιPlus)
  change ((pushforward f).rightDerivedFunctorPlus ⋙
        (restrictFunctor j).rightDerivedFunctorPlus).map (DerivedCategory.Plus.Q.map I.ιPlus) ≫
      (derivedOpenBaseChangeIso a b f j h).hom.app
        (DerivedCategory.Plus.Q.obj I.cochainComplexPlus) =
    (derivedOpenBaseChangeIso a b f j h).hom.app
        ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M) ≫ ν at hn
  have hs := openBaseChangeResolutionSourceIso_hom_comp f j M I
  have ht := openBaseChangeResolutionTargetIso_hom_comp a b M I J
  have hq := InjectiveResolution.mapCochainComparison_rightDerivedUnit
    (restrictFunctor a) I J (pushforward b)
  have hq' := congrArg (fun z => z ≫ (pushforward b).rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map
        (InjectiveResolution.mapCochainAugmentationPlus (restrictFunctor a) I)) ≫
    (pushforward b).rightDerivedFunctorPlus.map
      ((restrictFunctor a).rightDerivedFunctorPlusUnit.app I.cochainComplexPlus)) hq
  simp only [Category.assoc] at hq'
  have hm : DerivedCategory.Plus.Q.map
        (openBaseChangeResolutionMapPlus a b f j h M I J) ≫
      (openBaseChangeResolutionTargetIso a b M J).hom ≫ ν =
    DerivedCategory.Plus.Q.map
        ((NatTrans.mapCochainComplexPlus ((cartesianOpenBaseChange a b f j h).hom)).app
          I.cochainComplexPlus) ≫
      (Functor.rightDerivedFunctorPlusCompUnit (restrictFunctor a) (pushforward b)).app
        I.cochainComplexPlus := by
    dsimp only [ν]
    rw [ht]
    rw [openBaseChangeResolutionMapPlus, Functor.map_comp]
    simp only [Category.assoc]
    rw [hq', Functor.map_inv, IsIso.inv_hom_id_assoc,
      ← Functor.rightDerivedFunctorPlusCompUnit_app]
  calc
    _ = DerivedCategory.Plus.Q.map
        ((NatTrans.mapCochainComplexPlus ((cartesianOpenBaseChange a b f j h).hom)).app
          I.cochainComplexPlus) ≫
          (Functor.rightDerivedFunctorPlusCompUnit (restrictFunctor a) (pushforward b)).app
            I.cochainComplexPlus := by simpa only [Category.assoc] using hm
    _ = (Functor.rightDerivedFunctorPlusCompUnit (pushforward f) (restrictFunctor j)).app
        I.cochainComplexPlus ≫ (derivedOpenBaseChangeIso a b f j h).hom.app
          (DerivedCategory.Plus.Q.obj I.cochainComplexPlus) :=
      (derivedOpenBaseChangeIso_unit a b f j h I.cochainComplexPlus).symm
    _ = _ := by rw [← hs, Category.assoc, hn, ← Category.assoc]


private theorem openBaseChangeResolutionSourceIso_homology (n : ℕ) :
    let C := ((pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    (restrictFunctor j).map (I.isoRightDerivedObjCochain (pushforward f) n).hom ≫
        ((C.sc (n : ℤ)).mapHomologyIso (restrictFunctor j)).inv ≫
        (DerivedCategory.Plus.homologyFunctorFactors (A := V.Modules) (n : ℤ)).inv.app
          ((pushforward f ⋙ restrictFunctor j).mapCochainComplexPlus.obj I.cochainComplexPlus) ≫
        (DerivedCategory.Plus.homologyFunctor V.Modules (n : ℤ)).map
          (openBaseChangeResolutionSourceIso f j M I).hom =
      (restrictFunctor j).map
          (((pushforward f).rightDerivedSingleHomologyIso n).hom.app M) ≫
        ((restrictFunctor j).rightDerivedFunctorPlusHomologyIso (n : ℤ)).inv.app
          ((pushforward f).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) := by
  let F := pushforward f
  let J := restrictFunctor j
  let C := F.mapCochainComplexPlus.obj I.cochainComplexPlus
  let P := (DerivedCategory.Plus.homologyFunctorFactors (A := X.Modules) (n : ℤ)).app C
  let Q := (DerivedCategory.Plus.homologyFunctorFactors (A := V.Modules) (n : ℤ)).app
    (J.mapCochainComplexPlus.obj C)
  let d := (C.obj.sc (n : ℤ)).mapHomologyIso J
  let eJ := J.rightDerivedFunctorPlusHomologyIso (n : ℤ)
  let R := I.rightDerivedFunctorPlusIso F
  let HX := DerivedCategory.Plus.homologyFunctor X.Modules (n : ℤ)
  let HV := DerivedCategory.Plus.homologyFunctor V.Modules (n : ℤ)
  have hu : HV.map (J.rightDerivedFunctorPlusUnit.app C) ≫
      eJ.hom.app (DerivedCategory.Plus.Q.obj C) ≫ J.map P.hom = Q.hom ≫ d.hom :=
    J.rightDerivedFunctorPlusHomologyIso_unit (n : ℤ) C
  have hi : J.map P.inv ≫ eJ.inv.app (DerivedCategory.Plus.Q.obj C) =
      d.inv ≫ Q.inv ≫ HV.map (J.rightDerivedFunctorPlusUnit.app C) := by
    apply (cancel_mono (eJ.hom.app (DerivedCategory.Plus.Q.obj C) ≫ J.map P.hom)).mp
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    rw [← J.map_comp, Iso.inv_hom_id, J.map_id, hu]
    simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id]
  have hn := eJ.inv.naturality R.hom
  change J.map (HX.map R.hom) ≫ eJ.inv.app _ =
    eJ.inv.app (DerivedCategory.Plus.Q.obj C) ≫
      HV.map (J.rightDerivedFunctorPlus.map R.hom) at hn
  rw [Functor.rightDerivedSingleHomologyIso_hom_app (pushforward f) I n,
    InjectiveResolution.isoRightDerivedSingleHomology_hom]
  change J.map (I.isoRightDerivedObjCochain F n).hom ≫ d.inv ≫ Q.inv ≫
      HV.map (openBaseChangeResolutionSourceIso f j M I).hom =
    J.map ((I.isoRightDerivedObjCochain F n).hom ≫ P.inv ≫ HX.map R.hom) ≫ eJ.inv.app _
  rw [J.map_comp, J.map_comp]
  simp only [Category.assoc]
  rw [hn, ← Category.assoc (J.map P.inv), hi]
  simp only [Category.assoc]
  rw [← HV.map_comp]
  rfl



private theorem openBaseChangeResolutionTargetIso_homology (n : ℕ) :
    (DerivedCategory.Plus.homologyFunctor V.Modules (n : ℤ)).map
        (openBaseChangeResolutionTargetIso a b M J).hom ≫
      (DerivedCategory.Plus.homologyFunctor V.Modules (n : ℤ)).map
        ((pushforward b).rightDerivedFunctorPlus.map
          (((restrictFunctor a).rightDerivedFunctorPlusSingleIso 0).hom.app M)) ≫
      ((pushforward b).rightDerivedSingleHomologyIso n).inv.app ((restrictFunctor a).obj M) =
    (DerivedCategory.Plus.homologyFunctorFactors (A := V.Modules) (n : ℤ)).hom.app
        ((pushforward b).mapCochainComplexPlus.obj J.cochainComplexPlus) ≫
      (J.isoRightDerivedObjCochain (pushforward b) n).inv := by
  let B := pushforward b
  let HV := DerivedCategory.Plus.homologyFunctor V.Modules (n : ℤ)
  let P := (DerivedCategory.Plus.homologyFunctorFactors (A := V.Modules) (n : ℤ)).app
    (B.mapCochainComplexPlus.obj J.cochainComplexPlus)
  let R := J.rightDerivedFunctorPlusIso B
  let eA := (restrictFunctor a).rightDerivedFunctorPlusSingleIso 0
  let eB := B.rightDerivedSingleHomologyIso n
  have hB : eB.hom.app ((restrictFunctor a).obj M) =
      (J.isoRightDerivedObjCochain B n).hom ≫ P.inv ≫ HV.map R.hom := by
    rw [Functor.rightDerivedSingleHomologyIso_hom_app B J n]
    rfl
  apply (cancel_mono (eB.hom.app ((restrictFunctor a).obj M))).mp
  change HV.map (R.hom ≫ B.rightDerivedFunctorPlus.map (eA.inv.app M)) ≫
      HV.map (B.rightDerivedFunctorPlus.map (eA.hom.app M)) ≫
      eB.inv.app ((restrictFunctor a).obj M) ≫ eB.hom.app _ =
    P.hom ≫ (J.isoRightDerivedObjCochain B n).inv ≫ eB.hom.app _
  simp only [Iso.inv_hom_id_app]
  rw [hB]
  have hc : HV.map (B.rightDerivedFunctorPlus.map (eA.inv.app M)) ≫
      HV.map (B.rightDerivedFunctorPlus.map (eA.hom.app M)) = 𝟙 _ := by
    rw [← HV.map_comp, ← B.rightDerivedFunctorPlus.map_comp, Iso.inv_hom_id_app,
      B.rightDerivedFunctorPlus.map_id, HV.map_id]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  erw [Category.comp_id]
  rw [hc]
  erw [Category.comp_id]


/-- The actual native open higher-image comparison is computed by its original
cartesian map on the supplied coefficient resolution. -/
theorem higherDirectImageOpenRestrictionIso_app_resolution (n : ℕ) :
    let C := ((pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    (higherDirectImageOpenRestrictionIso a b f j h n).hom.app M =
      (restrictFunctor j).map (I.isoRightDerivedObjCochain (pushforward f) n).hom ≫
        ((C.sc (n : ℤ)).mapHomologyIso (restrictFunctor j)).inv ≫
        homologyMap (openBaseChangeResolutionMapPlus a b f j h M I J).hom (n : ℤ) ≫
        (J.isoRightDerivedObjCochain (pushforward b) n).inv := by
  let F := pushforward f
  let Jb := restrictFunctor j
  let A := restrictFunctor a
  let B := pushforward b
  let HV := DerivedCategory.Plus.homologyFunctor V.Modules (n : ℤ)
  let δ := (derivedOpenBaseChangeIso a b f j h).hom.app
    ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)
  let C := F.mapCochainComplexPlus.obj I.cochainComplexPlus
  let D := B.mapCochainComplexPlus.obj J.cochainComplexPlus
  let P := (DerivedCategory.Plus.homologyFunctorFactors (A := V.Modules) (n : ℤ)).app
    (Jb.mapCochainComplexPlus.obj C)
  let Q := (DerivedCategory.Plus.homologyFunctorFactors (A := V.Modules) (n : ℤ)).app D
  let d := (C.obj.sc (n : ℤ)).mapHomologyIso Jb
  let φ := openBaseChangeResolutionMapPlus a b f j h M I J
  have hs := openBaseChangeResolutionSourceIso_homology f j M I n
  have ht := openBaseChangeResolutionTargetIso_homology a b M J n
  have hr := congrArg HV.map (openBaseChangeResolutionMapPlus_derived a b f j h M I J)
  simp only [Functor.map_comp] at hr
  have hn := (DerivedCategory.Plus.homologyFunctorFactors (A := V.Modules) (n : ℤ)).hom.naturality φ
  change HV.map (DerivedCategory.Plus.Q.map φ) ≫ Q.hom =
    P.hom ≫ homologyMap φ.hom (n : ℤ) at hn
  have hn' : P.inv ≫ HV.map (DerivedCategory.Plus.Q.map φ) ≫ Q.hom =
      homologyMap φ.hom (n : ℤ) := by
    rw [hn, Iso.inv_hom_id_assoc]
  have he : (higherDirectImageOpenRestrictionIso a b f j h n).hom.app M =
      Jb.map (((pushforward f).rightDerivedSingleHomologyIso n).hom.app M) ≫
        (Jb.rightDerivedFunctorPlusHomologyIso (n : ℤ)).inv.app
          (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) ≫
        HV.map δ ≫ HV.map (B.rightDerivedFunctorPlus.map
          ((A.rightDerivedFunctorPlusSingleIso 0).hom.app M)) ≫
        (B.rightDerivedSingleHomologyIso n).inv.app (A.obj M) := by
    simp only [higherDirectImageOpenRestrictionIso, Iso.trans_hom, Iso.symm_hom,
      NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.comp_obj, Category.id_comp]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
  rw [he]
  change _ = Jb.map (I.isoRightDerivedObjCochain F n).hom ≫ d.inv ≫
    homologyMap φ.hom (n : ℤ) ≫ (J.isoRightDerivedObjCochain B n).inv
  rw [← Category.assoc (Jb.map _), ← hs]
  simp only [Category.assoc]
  rw [← Category.assoc (HV.map (openBaseChangeResolutionSourceIso f j M I).hom), ← hr]
  simp only [Category.assoc]
  rw [ht]
  change Jb.map (I.isoRightDerivedObjCochain F n).hom ≫ d.inv ≫ P.inv ≫
      HV.map (DerivedCategory.Plus.Q.map φ) ≫ Q.hom ≫
      (J.isoRightDerivedObjCochain B n).inv = _
  simpa only [Category.assoc] using congrArg
    (fun k => Jb.map (I.isoRightDerivedObjCochain F n).hom ≫ d.inv ≫ k ≫
      (J.isoRightDerivedObjCochain B n).inv) hn'


end AlgebraicGeometry.Scheme.Modules


