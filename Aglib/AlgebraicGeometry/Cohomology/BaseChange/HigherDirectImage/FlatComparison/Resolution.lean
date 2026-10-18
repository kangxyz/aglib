/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage.FlatComparison.Homology
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Derived.Resolution
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage

/-!
# The original flat higher-image map on supplied resolutions

The installed flat higher-direct-image comparison is computed by its original
cartesian map on supplied injective resolutions. Its source and target are
the original native resolution, derived-unit and homology comparisons. No
quasicoherence or finiteness condition is imposed.
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

/-- Retain the installed standard derived categories of actual module sheaves. -/
local instance flatComparisonStandard (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (h : IsPullback a b f j) [Flat a] [Flat j]
  (M : U.Modules) (I : InjectiveResolution M)
  (J : InjectiveResolution ((pullback a).obj M))

/-- The original source resolution comparison has its native exact-pullback homology form. -/
private theorem flatBaseChangeResolutionSourceIso_homology (n : ℕ) :
    let K := (pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus
    (pullback j).map (I.isoRightDerivedObjCochain (pushforward f) n).hom ≫
        ((K.obj.sc (n : ℤ)).mapHomologyIso (pullback j)).inv ≫
        (DerivedCategory.Plus.homologyFunctorFactors (A := V.Modules) (n : ℤ)).inv.app
          ((pushforward f ⋙ pullback j).mapCochainComplexPlus.obj I.cochainComplexPlus) ≫
        (DerivedCategory.Plus.homologyFunctor V.Modules (n : ℤ)).map
          (flatBaseChangeResolutionSourceIso f j M I).hom =
      (pullback j).map (((pushforward f).rightDerivedSingleHomologyIso n).hom.app M) ≫
        ((pullback j).rightDerivedFunctorPlusHomologyIso (n : ℤ)).inv.app
          ((pushforward f).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) := by
  let F := pushforward f
  let Pj := pullback j
  let K := F.mapCochainComplexPlus.obj I.cochainComplexPlus
  let P := (DerivedCategory.Plus.homologyFunctorFactors (A := X.Modules) (n : ℤ)).app K
  let Q := (DerivedCategory.Plus.homologyFunctorFactors (A := V.Modules) (n : ℤ)).app
    (Pj.mapCochainComplexPlus.obj K)
  let d := (K.obj.sc (n : ℤ)).mapHomologyIso Pj
  let E := Pj.rightDerivedFunctorPlusHomologyIso (n : ℤ)
  let R := I.rightDerivedFunctorPlusIso F
  let HX := DerivedCategory.Plus.homologyFunctor X.Modules (n : ℤ)
  let HV := DerivedCategory.Plus.homologyFunctor V.Modules (n : ℤ)
  have hsource : (flatBaseChangeResolutionSourceIso f j M I).hom =
      Pj.rightDerivedFunctorPlusUnit.app K ≫ Pj.rightDerivedFunctorPlus.map R.hom := by
    simp only [flatBaseChangeResolutionSourceIso, Iso.trans_hom, asIso_hom,
      Functor.mapIso_hom]
    rfl
  have hs : d.inv ≫ Q.inv ≫ HV.map (flatBaseChangeResolutionSourceIso f j M I).hom =
      Pj.map (P.inv ≫ HX.map R.hom) ≫
        E.inv.app (F.rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) := by
    rw [hsource]
    exact Pj.rightDerivedFunctorPlusHomologyIso_inv_unit_compIso (n : ℤ) K _ R
  rw [Functor.rightDerivedSingleHomologyIso_hom_app (pushforward f) I n,
    InjectiveResolution.isoRightDerivedSingleHomology_hom]
  change Pj.map (I.isoRightDerivedObjCochain F n).hom ≫ d.inv ≫ Q.inv ≫
      HV.map (flatBaseChangeResolutionSourceIso f j M I).hom =
    Pj.map ((I.isoRightDerivedObjCochain F n).hom ≫ P.inv ≫ HX.map R.hom) ≫ E.inv.app _
  conv_rhs => rw [Pj.map_comp]
  simpa only [Category.assoc] using congrArg
    (fun k => Pj.map (I.isoRightDerivedObjCochain F n).hom ≫ k) hs

/-- The original target resolution comparison cancels its native exact-single factors. -/
private theorem flatBaseChangeResolutionTargetIso_homology (n : ℕ) :
    (DerivedCategory.Plus.homologyFunctor V.Modules (n : ℤ)).map
        (flatBaseChangeResolutionTargetIso a b M J).hom ≫
      (DerivedCategory.Plus.homologyFunctor V.Modules (n : ℤ)).map
        ((pushforward b).rightDerivedFunctorPlus.map
          (((pullback a).rightDerivedFunctorPlusSingleIso 0).hom.app M)) ≫
      ((pushforward b).rightDerivedSingleHomologyIso n).inv.app ((pullback a).obj M) =
    (DerivedCategory.Plus.homologyFunctorFactors (A := V.Modules) (n : ℤ)).hom.app
        ((pushforward b).mapCochainComplexPlus.obj J.cochainComplexPlus) ≫
      (J.isoRightDerivedObjCochain (pushforward b) n).inv := by
  let B := pushforward b
  let HV := DerivedCategory.Plus.homologyFunctor V.Modules (n : ℤ)
  let P := (DerivedCategory.Plus.homologyFunctorFactors (A := V.Modules) (n : ℤ)).app
    (B.mapCochainComplexPlus.obj J.cochainComplexPlus)
  let R := J.rightDerivedFunctorPlusIso B
  let E := (pullback a).rightDerivedFunctorPlusSingleIso 0
  let EB := B.rightDerivedSingleHomologyIso n
  have hB : EB.hom.app ((pullback a).obj M) =
      (J.isoRightDerivedObjCochain B n).hom ≫ P.inv ≫ HV.map R.hom := by
    rw [Functor.rightDerivedSingleHomologyIso_hom_app B J n]
    rfl
  apply (cancel_mono (EB.hom.app ((pullback a).obj M))).mp
  change HV.map (R.hom ≫ B.rightDerivedFunctorPlus.map (E.inv.app M)) ≫
      HV.map (B.rightDerivedFunctorPlus.map (E.hom.app M)) ≫
      EB.inv.app ((pullback a).obj M) ≫ EB.hom.app _ =
    P.hom ≫ (J.isoRightDerivedObjCochain B n).inv ≫ EB.hom.app _
  simp only [Iso.inv_hom_id_app]
  rw [hB]
  have hc : HV.map (B.rightDerivedFunctorPlus.map (E.inv.app M)) ≫
      HV.map (B.rightDerivedFunctorPlus.map (E.hom.app M)) = 𝟙 _ := by
    rw [← HV.map_comp, ← B.rightDerivedFunctorPlus.map_comp, Iso.inv_hom_id_app,
      B.rightDerivedFunctorPlus.map_id, HV.map_id]
  simp only [Functor.map_comp, Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc]
  erw [Category.comp_id]
  rw [hc]
  erw [Category.comp_id]

omit [Flat a] in
/-- The original flat higher-image comparison is the original resolution map on homology,
through the native supplied-resolution and exact-pullback comparisons. -/
theorem higherDirectImageFlatBaseChangeMap_app_resolution (n : ℕ) :
    let := flat_cartesian_baseChange a b f j h
    let K := (pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus
    (higherDirectImageFlatBaseChangeMap a b f j h n).app M =
      (pullback j).map (I.isoRightDerivedObjCochain (pushforward f) n).hom ≫
        ((K.obj.sc (n : ℤ)).mapHomologyIso (pullback j)).inv ≫
        homologyMap (flatBaseChangeResolutionMapPlus a b f j h M I J).hom (n : ℤ) ≫
        (J.isoRightDerivedObjCochain (pushforward b) n).inv := by
  let := flat_cartesian_baseChange a b f j h
  let F := pushforward f
  let Pj := pullback j
  let A := pullback a
  let B := pushforward b
  let HV := DerivedCategory.Plus.homologyFunctor V.Modules (n : ℤ)
  let δ := (derivedFlatBaseChangeMap a b f j h).app
    ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)
  let K := F.mapCochainComplexPlus.obj I.cochainComplexPlus
  let D := B.mapCochainComplexPlus.obj J.cochainComplexPlus
  let P := (DerivedCategory.Plus.homologyFunctorFactors (A := V.Modules) (n : ℤ)).app
    (Pj.mapCochainComplexPlus.obj K)
  let Q := (DerivedCategory.Plus.homologyFunctorFactors (A := V.Modules) (n : ℤ)).app D
  let d := (K.obj.sc (n : ℤ)).mapHomologyIso Pj
  let φ := flatBaseChangeResolutionMapPlus a b f j h M I J
  have hs := flatBaseChangeResolutionSourceIso_homology f j M I n
  have ht := flatBaseChangeResolutionTargetIso_homology a b M J n
  have hr := congrArg HV.map (flatBaseChangeResolutionMapPlus_derived a b f j h M I J)
  simp only [Functor.map_comp] at hr
  have hn := (DerivedCategory.Plus.homologyFunctorFactors (A := V.Modules) (n : ℤ)).hom.naturality φ
  change HV.map (DerivedCategory.Plus.Q.map φ) ≫ Q.hom =
    P.hom ≫ homologyMap φ.hom (n : ℤ) at hn
  have hn' : P.inv ≫ HV.map (DerivedCategory.Plus.Q.map φ) ≫ Q.hom =
      homologyMap φ.hom (n : ℤ) := by
    rw [hn, Iso.inv_hom_id_assoc]
  have he : (higherDirectImageFlatBaseChangeMap a b f j h n).app M =
      Pj.map (((pushforward f).rightDerivedSingleHomologyIso n).hom.app M) ≫
        (Pj.rightDerivedFunctorPlusHomologyIso (n : ℤ)).inv.app
          (F.rightDerivedFunctorPlus.obj ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) ≫
        HV.map δ ≫ HV.map (B.rightDerivedFunctorPlus.map
          ((A.rightDerivedFunctorPlusSingleIso 0).hom.app M)) ≫
        (B.rightDerivedSingleHomologyIso n).inv.app (A.obj M) := by
    simpa only [derivedPushforwardPlus] using
      higherDirectImageFlatBaseChangeMap_app a b f j h n M
  rw [he]
  change _ = Pj.map (I.isoRightDerivedObjCochain F n).hom ≫ d.inv ≫
    homologyMap φ.hom (n : ℤ) ≫ (J.isoRightDerivedObjCochain B n).inv
  rw [← Category.assoc (Pj.map _), ← hs]
  simp only [Category.assoc]
  rw [← Category.assoc (HV.map (flatBaseChangeResolutionSourceIso f j M I).hom), ← hr]
  simp only [Category.assoc]
  rw [ht]
  change Pj.map (I.isoRightDerivedObjCochain F n).hom ≫ d.inv ≫ P.inv ≫
    HV.map (DerivedCategory.Plus.Q.map φ) ≫ Q.hom ≫
      (J.isoRightDerivedObjCochain B n).inv = _
  simpa only [Category.assoc] using congrArg
    (fun k => Pj.map (I.isoRightDerivedObjCochain F n).hom ≫ d.inv ≫ k ≫
      (J.isoRightDerivedObjCochain B n).inv) hn'

end AlgebraicGeometry.Scheme.Modules
