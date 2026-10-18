/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Derived.Restriction
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage
public import Aglib.Algebra.Homology.CochainComplexPlus.NatTrans

/-!
# The original flat comparison on an open change of base

The actual ordinary open comparison is the geometric pullback mate after
transport by the original restriction/pullback isomorphisms. The installed
derived units and their original homology and single comparisons preserve
this identity for all higher direct images of arbitrary module coefficients.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicGeometry

universe u
namespace AlgebraicGeometry.Scheme.Modules

/-- All comparisons use the installed standard derived categories. -/
local instance flatOpenStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

section DerivedUnits

variable {X Y Z : Scheme.{u}}

private theorem compUnit_iso_right (F : X.Modules ⥤ Y.Modules) [F.Additive]
    (G G' : Y.Modules ⥤ Z.Modules) [G.Additive] [G'.Additive] (e : G ≅ G')
    (K : CochainComplex.Plus X.Modules) :
    (Functor.rightDerivedFunctorPlusCompUnit F G).app K ≫
        (G.rightDerivedFunctorPlusIso e).hom.app
          (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) =
      DerivedCategory.Plus.Q.map
          ((NatIso.mapCochainComplexPlus e).hom.app (F.mapCochainComplexPlus.obj K)) ≫
        (Functor.rightDerivedFunctorPlusCompUnit F G').app K := by
  have hn := (G.rightDerivedFunctorPlusIso e).hom.naturality
    (F.rightDerivedFunctorPlusUnit.app K)
  change G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K) ≫
      (G.rightDerivedFunctorPlusIso e).hom.app
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) =
    (G.rightDerivedFunctorPlusIso e).hom.app
      (DerivedCategory.Plus.Q.obj (F.mapCochainComplexPlus.obj K)) ≫
      G'.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K) at hn
  rw [Functor.rightDerivedFunctorPlusCompUnit_app,
    Functor.rightDerivedFunctorPlusCompUnit_app]
  rw [Category.assoc, hn, ← Category.assoc,
    G.rightDerivedFunctorPlusIso_hom_app e (F.mapCochainComplexPlus.obj K)]
  simp only [Category.assoc]

private theorem compUnit_iso_left (F F' : X.Modules ⥤ Y.Modules)
    [F.Additive] [F'.Additive] (e : F ≅ F')
    (G : Y.Modules ⥤ Z.Modules) [G.Additive] (K : CochainComplex.Plus X.Modules) :
    (Functor.rightDerivedFunctorPlusCompUnit F G).app K ≫
        G.rightDerivedFunctorPlus.map
          ((F.rightDerivedFunctorPlusIso e).hom.app (DerivedCategory.Plus.Q.obj K)) =
      DerivedCategory.Plus.Q.map (G.mapCochainComplexPlus.map
          ((NatIso.mapCochainComplexPlus e).hom.app K)) ≫
        (Functor.rightDerivedFunctorPlusCompUnit F' G).app K := by
  let ξ := (NatIso.mapCochainComplexPlus e).hom.app K
  have hn := G.rightDerivedFunctorPlusUnit.naturality ξ
  change DerivedCategory.Plus.Q.map (G.mapCochainComplexPlus.map ξ) ≫
      G.rightDerivedFunctorPlusUnit.app (F'.mapCochainComplexPlus.obj K) =
    G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) ≫
      G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ξ) at hn
  rw [Functor.rightDerivedFunctorPlusCompUnit_app,
    Functor.rightDerivedFunctorPlusCompUnit_app]
  rw [Category.assoc, ← Functor.map_comp,
    F.rightDerivedFunctorPlusIso_hom_app e K, Functor.map_comp]
  simpa only [Category.assoc] using congrArg
    (fun t => t ≫ G.rightDerivedFunctorPlus.map (F'.rightDerivedFunctorPlusUnit.app K)) hn.symm

end DerivedUnits

section ExactIso

variable {X Y : Scheme.{u}} (F G : X.Modules ⥤ Y.Modules)
  [F.Additive] [G.Additive] [F.PreservesHomology] [G.PreservesHomology] (e : F ≅ G)

private theorem derivedIso_homology (n : ℤ) :
    Functor.whiskerRight (F.rightDerivedFunctorPlusIso e).hom
        (DerivedCategory.Plus.homologyFunctor Y.Modules n) ≫
        (G.rightDerivedFunctorPlusHomologyIso n).hom =
      (F.rightDerivedFunctorPlusHomologyIso n).hom ≫
        Functor.whiskerLeft (DerivedCategory.Plus.homologyFunctor X.Modules n) e.hom := by
  apply Localization.natTrans_ext (DerivedCategory.Plus.Q (C := X.Modules))
    (CochainComplex.Plus.quasiIso X.Modules)
  intro K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  let H := DerivedCategory.Plus.homologyFunctor Y.Modules n
  let P := (DerivedCategory.Plus.homologyFunctorFactors (A := X.Modules) n).app K
  let PF := (DerivedCategory.Plus.homologyFunctorFactors (A := Y.Modules) n).app
    (F.mapCochainComplexPlus.obj K)
  let PG := (DerivedCategory.Plus.homologyFunctorFactors (A := Y.Modules) n).app
    (G.mapCochainComplexPlus.obj K)
  let ξ := (NatIso.mapCochainComplexPlus e).hom.app K
  let EF := F.rightDerivedFunctorPlusHomologyIso n
  let EG := G.rightDerivedFunctorPlusHomologyIso n
  let : IsIso F.rightDerivedFunctorPlusUnit :=
    F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  have hu := congrArg H.map (F.rightDerivedFunctorPlusIso_hom_app e K)
  simp only [Functor.map_comp] at hu
  have hF := F.rightDerivedFunctorPlusHomologyIso_unit n K
  change H.map (F.rightDerivedFunctorPlusUnit.app K) ≫
      EF.hom.app (DerivedCategory.Plus.Q.obj K) ≫ F.map P.hom =
    PF.hom ≫ ((K.obj.sc n).mapHomologyIso F).hom at hF
  have hG := G.rightDerivedFunctorPlusHomologyIso_unit n K
  change H.map (G.rightDerivedFunctorPlusUnit.app K) ≫
      EG.hom.app (DerivedCategory.Plus.Q.obj K) ≫ G.map P.hom =
    PG.hom ≫ ((K.obj.sc n).mapHomologyIso G).hom at hG
  have hn := e.hom.naturality P.hom
  change F.map P.hom ≫ e.hom.app (K.obj.homology n) =
    e.hom.app ((DerivedCategory.Plus.homologyFunctor X.Modules n).obj
      (DerivedCategory.Plus.Q.obj K)) ≫ G.map P.hom at hn
  have hP := (DerivedCategory.Plus.homologyFunctorFactors (A := Y.Modules) n).hom.naturality ξ
  change H.map (DerivedCategory.Plus.Q.map ξ) ≫ PG.hom =
    PF.hom ≫ homologyMap ξ.hom n at hP
  have hSC := NatTrans.app_homology e.hom (K.obj.sc n)
  change e.hom.app (K.obj.homology n) =
    ((K.obj.sc n).mapHomologyIso F).inv ≫ homologyMap ξ.hom n ≫
      ((K.obj.sc n).mapHomologyIso G).hom at hSC
  apply (cancel_epi (H.map (F.rightDerivedFunctorPlusUnit.app K))).mp
  apply (cancel_mono (G.map P.hom)).mp
  simp only [Category.assoc]
  conv_lhs =>
    rw [← Category.assoc (H.map (F.rightDerivedFunctorPlusUnit.app K))
      (H.map ((F.rightDerivedFunctorPlusIso e).hom.app (DerivedCategory.Plus.Q.obj K))), hu]
    simp only [Category.assoc]
    rw [hG]
    rw [← Category.assoc (H.map (DerivedCategory.Plus.Q.map ξ)) PG.hom, hP]
    simp only [Category.assoc]
  conv_rhs =>
    rw [← hn]
    rw [← Category.assoc (EF.hom.app (DerivedCategory.Plus.Q.obj K)) (F.map P.hom)]
    rw [← Category.assoc (H.map (F.rightDerivedFunctorPlusUnit.app K))
      (EF.hom.app (DerivedCategory.Plus.Q.obj K) ≫ F.map P.hom), hF]
    rw [hSC]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]

private theorem derivedIso_homology_inv (n : ℤ) (K : DerivedCategory.Plus X.Modules) :
    e.hom.app ((DerivedCategory.Plus.homologyFunctor X.Modules n).obj K) ≫
        (G.rightDerivedFunctorPlusHomologyIso n).inv.app K =
      (F.rightDerivedFunctorPlusHomologyIso n).inv.app K ≫
        (DerivedCategory.Plus.homologyFunctor Y.Modules n).map
          ((F.rightDerivedFunctorPlusIso e).hom.app K) := by
  have he := congr_app (derivedIso_homology F G e n) K
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at he
  apply (cancel_mono ((G.rightDerivedFunctorPlusHomologyIso n).hom.app K)).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [he, Iso.inv_hom_id_app_assoc]
  erw [Category.comp_id]

private def singleComplexIso (M : X.Modules) :
    F.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus X.Modules 0).obj M) ≅
      (CochainComplex.singleFunctorPlus Y.Modules 0).obj (F.obj M) :=
  (CochainComplex.plus Y.Modules).isoMk
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app M)

private theorem derivedIso_single (M : X.Modules) :
    (F.rightDerivedFunctorPlusIso e).hom.app
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) ≫
        (G.rightDerivedFunctorPlusSingleIso 0).hom.app M =
      (F.rightDerivedFunctorPlusSingleIso 0).hom.app M ≫
        (DerivedCategory.Plus.singleFunctor Y.Modules 0).map (e.hom.app M) := by
  let K := (CochainComplex.singleFunctorPlus X.Modules 0).obj M
  let ξ := (NatIso.mapCochainComplexPlus e).hom.app K
  let sF := singleComplexIso F M
  let sG := singleComplexIso G M
  let : IsIso F.rightDerivedFunctorPlusUnit :=
    F.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  have hs : ξ ≫ sG.hom = sF.hom ≫
      (CochainComplex.singleFunctorPlus Y.Modules 0).map (e.hom.app M) := by
    apply ObjectProperty.hom_ext
    change (e.hom.mapHomologicalComplex (.up ℤ)).app
        ((HomologicalComplex.single X.Modules (.up ℤ) 0).obj M) ≫
        (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app M =
      (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M ≫
        (HomologicalComplex.single Y.Modules (.up ℤ) 0).map (e.hom.app M)
    rw [HomologicalComplex.natTransMapHomologicalComplex_app_single_obj]
    simp only [Category.assoc, Iso.inv_hom_id_app]
    erw [Category.comp_id]
  apply (cancel_epi (F.rightDerivedFunctorPlusUnit.app K)).mp
  change F.rightDerivedFunctorPlusUnit.app K ≫
      (F.rightDerivedFunctorPlusIso e).hom.app (DerivedCategory.Plus.Q.obj K) ≫
      (G.rightDerivedFunctorPlusSingleIso 0).hom.app M =
    F.rightDerivedFunctorPlusUnit.app K ≫
      (F.rightDerivedFunctorPlusSingleIso 0).hom.app M ≫
      (DerivedCategory.Plus.singleFunctor Y.Modules 0).map (e.hom.app M)
  rw [← Category.assoc, F.rightDerivedFunctorPlusIso_hom_app e K, Category.assoc,
    G.rightDerivedFunctorPlusSingleIso_unit 0 M,
    ← Category.assoc (F.rightDerivedFunctorPlusUnit.app K),
    F.rightDerivedFunctorPlusSingleIso_unit 0 M]
  change DerivedCategory.Plus.Q.map ξ ≫ DerivedCategory.Plus.Q.map sG.hom =
    DerivedCategory.Plus.Q.map sF.hom ≫
      DerivedCategory.Plus.Q.map
        ((CochainComplex.singleFunctorPlus Y.Modules 0).map (e.hom.app M))
  simpa only [Functor.map_comp] using
    congrArg (DerivedCategory.Plus.Q (C := Y.Modules)).map hs

end ExactIso

section OpenComparison

variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [IsOpenImmersion a] [IsOpenImmersion j] (h : IsPullback a b f j)

private theorem derivedFlat_open :
    derivedFlatBaseChangeMap a b f j h =
      Functor.whiskerLeft (pushforward f).rightDerivedFunctorPlus
          ((pullback j).rightDerivedFunctorPlusIso (restrictFunctorIsoPullback j).symm).hom ≫
        (derivedOpenBaseChangeIso a b f j h).hom ≫
        Functor.whiskerRight
          ((restrictFunctor a).rightDerivedFunctorPlusIso (restrictFunctorIsoPullback a)).hom
          (pushforward b).rightDerivedFunctorPlus := by
  let F := pushforward f
  let J := pullback j
  let Jr := restrictFunctor j
  let A := pullback a
  let Ar := restrictFunctor a
  let B := pushforward b
  let eJ := (restrictFunctorIsoPullback j).symm
  let eA := restrictFunctorIsoPullback a
  let := F.isRightDerivedFunctor_comp_of_preservesHomology J
  apply Functor.rightDerived_ext _ (Functor.rightDerivedFunctorPlusCompUnit F J)
    (CochainComplex.Plus.quasiIso U.Modules)
  ext K : 2
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [derivedFlatBaseChangeMap_unit a b f j h K]
  change DerivedCategory.Plus.Q.map
      ((NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap a b f j h)).app K) ≫
      (Functor.rightDerivedFunctorPlusCompUnit A B).app K =
    (Functor.rightDerivedFunctorPlusCompUnit F J).app K ≫
      (J.rightDerivedFunctorPlusIso eJ).hom.app
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) ≫
      (derivedOpenBaseChangeIso a b f j h).hom.app (DerivedCategory.Plus.Q.obj K) ≫
      B.rightDerivedFunctorPlus.map
        ((Ar.rightDerivedFunctorPlusIso eA).hom.app (DerivedCategory.Plus.Q.obj K))
  have hj := compUnit_iso_right F J Jr eJ K
  have ha := compUnit_iso_left Ar A eA B K
  have ho := derivedOpenBaseChangeIso_unit a b f j h K
  have hc :
      (NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap a b f j h)).app K =
        (NatIso.mapCochainComplexPlus eJ).hom.app (F.mapCochainComplexPlus.obj K) ≫
          (NatIso.mapCochainComplexPlus (cartesianOpenBaseChange a b f j h)).hom.app K ≫
          B.mapCochainComplexPlus.map ((NatIso.mapCochainComplexPlus eA).hom.app K) := by
    apply ObjectProperty.hom_ext
    apply HomologicalComplex.hom_ext
    intro k
    exact (cartesianOpenBaseChange_pullback a b f j h (K.obj.X k)).symm
  rw [← Category.assoc ((Functor.rightDerivedFunctorPlusCompUnit F J).app K)
      (((J.rightDerivedFunctorPlusIso eJ).hom).app
        (F.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K))), hj]
  simp only [Category.assoc]
  rw [← Category.assoc ((Functor.rightDerivedFunctorPlusCompUnit F Jr).app K)
      ((derivedOpenBaseChangeIso a b f j h).hom.app (DerivedCategory.Plus.Q.obj K)), ho]
  simp only [Category.assoc]
  rw [ha, hc]
  simp only [Functor.map_comp, Category.assoc]

private theorem higherOpen_app_model (n : ℕ) (M : U.Modules) :
    (higherDirectImageOpenRestrictionIso a b f j h n).hom.app M =
      (restrictFunctor j).map (((pushforward f).rightDerivedSingleHomologyIso n).hom.app M) ≫
        ((restrictFunctor j).rightDerivedFunctorPlusHomologyIso (n : ℤ)).inv.app
          ((pushforward f).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) ≫
        (DerivedCategory.Plus.homologyFunctor V.Modules (n : ℤ)).map
          ((derivedOpenBaseChangeIso a b f j h).hom.app
            ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) ≫
        (DerivedCategory.Plus.homologyFunctor V.Modules (n : ℤ)).map
          ((pushforward b).rightDerivedFunctorPlus.map
            (((restrictFunctor a).rightDerivedFunctorPlusSingleIso 0).hom.app M)) ≫
        ((pushforward b).rightDerivedSingleHomologyIso n).inv.app ((restrictFunctor a).obj M) := by
  simp only [higherDirectImageOpenRestrictionIso, Iso.trans_hom, Iso.symm_hom,
    NatTrans.comp_app, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.comp_obj, Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]

/-- On an open change of base, the original flat higher-image map is the native open
restriction comparison transported by the original restriction/pullback isomorphisms. -/
@[reassoc]
theorem higherDirectImageFlatBaseChangeMap_eq_openRestriction (n : ℕ) (M : U.Modules) :
    (higherDirectImageFlatBaseChangeMap a b f j h n).app M =
      (restrictFunctorIsoPullback j).inv.app (((pushforward f).rightDerived n).obj M) ≫
        (higherDirectImageOpenRestrictionIso a b f j h n).hom.app M ≫
        ((pushforward b).rightDerived n).map ((restrictFunctorIsoPullback a).hom.app M) := by
  let F := pushforward f
  let J := pullback j
  let Jr := restrictFunctor j
  let A := pullback a
  let Ar := restrictFunctor a
  let B := pushforward b
  let H₀ := DerivedCategory.Plus.homologyFunctor X.Modules (n : ℤ)
  let H := DerivedCategory.Plus.homologyFunctor V.Modules (n : ℤ)
  let K := (DerivedCategory.Plus.singleFunctor U.Modules 0).obj M
  let eF := F.rightDerivedSingleHomologyIso n
  let eB := B.rightDerivedSingleHomologyIso n
  let eJ := (restrictFunctorIsoPullback j).symm
  let eA := restrictFunctorIsoPullback a
  have hj := derivedIso_homology_inv J Jr eJ (n : ℤ) (F.rightDerivedFunctorPlus.obj K)
  have ha := derivedIso_single Ar A eA M
  have hnJ := eJ.hom.naturality (eF.hom.app M)
  change J.map (eF.hom.app M) ≫
      eJ.hom.app (H₀.obj (F.rightDerivedFunctorPlus.obj K)) =
    eJ.hom.app ((F.rightDerived n).obj M) ≫ Jr.map (eF.hom.app M) at hnJ
  have hnB := eB.inv.naturality (eA.hom.app M)
  change H.map (B.rightDerivedFunctorPlus.map
      ((DerivedCategory.Plus.singleFunctor W.Modules 0).map (eA.hom.app M))) ≫
      eB.inv.app (A.obj M) =
    eB.inv.app (Ar.obj M) ≫ (B.rightDerived n).map (eA.hom.app M) at hnB
  rw [higherDirectImageFlatBaseChangeMap_app, higherOpen_app_model a b f j h n M,
    derivedFlat_open a b f j h]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc]
  change J.map (eF.hom.app M) ≫
      (J.rightDerivedFunctorPlusHomologyIso (n : ℤ)).inv.app
        (F.rightDerivedFunctorPlus.obj K) ≫
      H.map ((J.rightDerivedFunctorPlusIso eJ).hom.app (F.rightDerivedFunctorPlus.obj K)) ≫
      H.map ((derivedOpenBaseChangeIso a b f j h).hom.app K) ≫
      H.map (B.rightDerivedFunctorPlus.map ((Ar.rightDerivedFunctorPlusIso eA).hom.app K)) ≫
      H.map (B.rightDerivedFunctorPlus.map ((A.rightDerivedFunctorPlusSingleIso 0).hom.app M)) ≫
      eB.inv.app (A.obj M) =
    eJ.hom.app ((F.rightDerived n).obj M) ≫ Jr.map (eF.hom.app M) ≫
      (Jr.rightDerivedFunctorPlusHomologyIso (n : ℤ)).inv.app
        (F.rightDerivedFunctorPlus.obj K) ≫
      H.map ((derivedOpenBaseChangeIso a b f j h).hom.app K) ≫
      H.map (B.rightDerivedFunctorPlus.map ((Ar.rightDerivedFunctorPlusSingleIso 0).hom.app M)) ≫
      eB.inv.app (Ar.obj M) ≫ (B.rightDerived n).map (eA.hom.app M)
  rw [← Category.assoc ((J.rightDerivedFunctorPlusHomologyIso (n : ℤ)).inv.app
      (F.rightDerivedFunctorPlus.obj K))
      (H.map ((J.rightDerivedFunctorPlusIso eJ).hom.app (F.rightDerivedFunctorPlus.obj K))),
    ← hj]
  simp only [Category.assoc]
  rw [← Category.assoc (J.map (eF.hom.app M))
      (eJ.hom.app (H₀.obj (F.rightDerivedFunctorPlus.obj K))), hnJ]
  simp only [Category.assoc]
  rw [← H.map_comp_assoc
      (B.rightDerivedFunctorPlus.map ((Ar.rightDerivedFunctorPlusIso eA).hom.app K))
      (B.rightDerivedFunctorPlus.map ((A.rightDerivedFunctorPlusSingleIso 0).hom.app M)),
    ← B.rightDerivedFunctorPlus.map_comp, ha, B.rightDerivedFunctorPlus.map_comp, H.map_comp]
  simp only [Category.assoc]
  rw [hnB]

end OpenComparison

end AlgebraicGeometry.Scheme.Modules
