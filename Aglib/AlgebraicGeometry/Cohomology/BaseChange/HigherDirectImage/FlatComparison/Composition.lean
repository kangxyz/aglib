/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Derived.Restriction
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.HigherDirectImage
public import Aglib.Algebra.Homology.CochainComplexPlus.NatTrans
public import Aglib.Algebra.Homology.ShortComplex.MapHomology

/-!
# Composition of the original flat higher-image comparisons

The original derived flat comparison pastes through its native pullback
composition isomorphisms. Its installed exact-functor homology and single
comparisons preserve those same composition maps, so the actual higher-image
maps paste for every module coefficient, without finiteness or quasicoherence.
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
local instance flatPastingStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

private def flatPullbackCompInverseIso {U V X : Scheme.{u}} (a : U ⟶ V) (j : V ⟶ X) :
    pullback (a ≫ j) ≅ pullback j ⋙ pullback a := (pullbackComp a j).symm

private def derivedFlatPullbackCompInverseIso {U V X : Scheme.{u}}
    (a : U ⟶ V) (j : V ⟶ X) [Flat a] [Flat j] :
    (pullback (a ≫ j)).rightDerivedFunctorPlus ≅
      (pullback j).rightDerivedFunctorPlus ⋙ (pullback a).rightDerivedFunctorPlus :=
  (derivedFlatPullbackPlusCompIso a j).symm

private theorem derivedFlatPullbackCompInverseIso_unit {U V X : Scheme.{u}}
    (a : U ⟶ V) (j : V ⟶ X) [Flat a] [Flat j]
    (K : CochainComplex.Plus X.Modules) :
    (pullback (a ≫ j)).rightDerivedFunctorPlusUnit.app K ≫
        (derivedFlatPullbackCompInverseIso a j).hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map
          ((NatIso.mapCochainComplexPlus (flatPullbackCompInverseIso a j)).hom.app K) ≫
        (Functor.rightDerivedFunctorPlusCompUnit (pullback j) (pullback a)).app K := by
  let E := derivedFlatPullbackPlusCompIso a j
  let ξ := (NatIso.mapCochainComplexPlus (pullbackComp a j)).app K
  have he := derivedFlatPullbackPlusCompIso_unit a j K
  change (Functor.rightDerivedFunctorPlusCompUnit (pullback j) (pullback a)).app K ≫
    E.hom.app (DerivedCategory.Plus.Q.obj K) =
      DerivedCategory.Plus.Q.map ξ.hom ≫
        (pullback (a ≫ j)).rightDerivedFunctorPlusUnit.app K at he
  change (pullback (a ≫ j)).rightDerivedFunctorPlusUnit.app K ≫
      E.inv.app (DerivedCategory.Plus.Q.obj K) =
    DerivedCategory.Plus.Q.map ξ.inv ≫
      (Functor.rightDerivedFunctorPlusCompUnit (pullback j) (pullback a)).app K
  apply (cancel_epi (DerivedCategory.Plus.Q.map ξ.hom)).mp
  rw [← Category.assoc (DerivedCategory.Plus.Q.map ξ.hom), ← he]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  rw [← Functor.map_comp_assoc, ξ.hom_inv_id]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]

section SingleComplex

variable {X Y Z : Scheme.{u}} (F : X.Modules ⥤ Y.Modules) [F.Additive]

private def singleComplexIso (M : X.Modules) :
    F.mapCochainComplexPlus.obj ((CochainComplex.singleFunctorPlus X.Modules 0).obj M) ≅
      (CochainComplex.singleFunctorPlus Y.Modules 0).obj (F.obj M) :=
  (CochainComplex.plus Y.Modules).isoMk
    ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).app M)

private theorem singleComplexIso_unit [F.PreservesHomology] (M : X.Modules) :
    F.rightDerivedFunctorPlusUnit.app ((CochainComplex.singleFunctorPlus X.Modules 0).obj M) ≫
        (F.rightDerivedFunctorPlusSingleIso 0).hom.app M =
      DerivedCategory.Plus.Q.map (singleComplexIso F M).hom :=
  F.rightDerivedFunctorPlusSingleIso_unit 0 M

private theorem singleComplexIso_comp (G : Y.Modules ⥤ Z.Modules) [G.Additive]
    (M : X.Modules) :
    (singleComplexIso (F ⋙ G) M).hom =
      G.mapCochainComplexPlus.map (singleComplexIso F M).hom ≫
        (singleComplexIso G (F.obj M)).hom := by
  apply ObjectProperty.hom_ext
  change (HomologicalComplex.singleMapHomologicalComplex (F ⋙ G) (.up ℤ) 0).hom.app M =
    (G.mapHomologicalComplex (.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M) ≫
      (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app (F.obj M)
  simpa only [Functor.mapHomologicalComplexCompIso, NatIso.mapHomologicalComplex,
    Iso.refl_inv, NatTrans.mapHomologicalComplex_id, NatTrans.id_app, Category.id_comp] using
    HomologicalComplex.singleMapHomologicalComplex_comp_hom_app F G (.up ℤ) (0 : ℤ) M

private theorem singleComplexIso_naturality {G : X.Modules ⥤ Y.Modules} [G.Additive]
    (τ : F ⟶ G) (M : X.Modules) :
    (NatTrans.mapCochainComplexPlus τ).app ((CochainComplex.singleFunctorPlus X.Modules 0).obj M) ≫
        (singleComplexIso G M).hom =
      (singleComplexIso F M).hom ≫
        (CochainComplex.singleFunctorPlus Y.Modules 0).map (τ.app M) := by
  apply ObjectProperty.hom_ext
  change (τ.mapHomologicalComplex (.up ℤ)).app
        ((HomologicalComplex.single X.Modules (.up ℤ) 0).obj M) ≫
      (HomologicalComplex.singleMapHomologicalComplex G (.up ℤ) 0).hom.app M =
    (HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app M ≫
      (HomologicalComplex.single Y.Modules (.up ℤ) 0).map (τ.app M)
  rw [HomologicalComplex.natTransMapHomologicalComplex_app_single_obj]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]

end SingleComplex

section CompositeSingle

variable {X Y Z : Scheme.{u}} (F : X.Modules ⥤ Y.Modules) (G : Y.Modules ⥤ Z.Modules)
  [F.Additive] [G.Additive] [F.PreservesHomology] [G.PreservesHomology]

private theorem compositeSingleUnit (M : X.Modules) :
    (Functor.rightDerivedFunctorPlusCompUnit F G).app
          ((CochainComplex.singleFunctorPlus X.Modules 0).obj M) ≫
        G.rightDerivedFunctorPlus.map ((F.rightDerivedFunctorPlusSingleIso 0).hom.app M) ≫
        (G.rightDerivedFunctorPlusSingleIso 0).hom.app (F.obj M) =
      DerivedCategory.Plus.Q.map (singleComplexIso (F ⋙ G) M).hom := by
  let K := (CochainComplex.singleFunctorPlus X.Modules 0).obj M
  let eF := F.rightDerivedFunctorPlusSingleIso 0
  let eG := G.rightDerivedFunctorPlusSingleIso 0
  let sF := singleComplexIso F M
  let sG := singleComplexIso G (F.obj M)
  have hF := singleComplexIso_unit F M
  have hG := singleComplexIso_unit G (F.obj M)
  have hn := G.rightDerivedFunctorPlusUnit.naturality sF.hom
  change DerivedCategory.Plus.Q.map (G.mapCochainComplexPlus.map sF.hom) ≫
      G.rightDerivedFunctorPlusUnit.app
        ((CochainComplex.singleFunctorPlus Y.Modules 0).obj (F.obj M)) =
    G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K) ≫
      G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map sF.hom) at hn
  rw [Functor.rightDerivedFunctorPlusCompUnit_app]
  simp only [Category.assoc]
  rw [← Category.assoc (G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnit.app K))
    (G.rightDerivedFunctorPlus.map (eF.hom.app M)), ← Functor.map_comp, hF]
  rw [← Category.assoc (G.rightDerivedFunctorPlusUnit.app (F.mapCochainComplexPlus.obj K))
    (G.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map sF.hom)), ← hn]
  simp only [Category.assoc]
  rw [hG, ← Functor.map_comp, ← singleComplexIso_comp F G M]

end CompositeSingle

section DerivedSingle

variable {U V X : Scheme.{u}} (a : U ⟶ V) (j : V ⟶ X)
  [Flat a] [Flat j] (M : X.Modules)

private theorem derivedFlatPullbackCompInverseIso_single :
    (derivedFlatPullbackCompInverseIso a j).hom.app
          ((DerivedCategory.Plus.singleFunctor X.Modules 0).obj M) ≫
        (pullback a).rightDerivedFunctorPlus.map
          (((pullback j).rightDerivedFunctorPlusSingleIso 0).hom.app M) ≫
        ((pullback a).rightDerivedFunctorPlusSingleIso 0).hom.app
          ((pullback j).obj M) =
      ((pullback (a ≫ j)).rightDerivedFunctorPlusSingleIso 0).hom.app M ≫
        (DerivedCategory.Plus.singleFunctor U.Modules 0).map
          ((flatPullbackCompInverseIso a j).hom.app M) := by
  let J := pullback j
  let A := pullback a
  let JA := pullback (a ≫ j)
  let K := (CochainComplex.singleFunctorPlus X.Modules 0).obj M
  let e := derivedFlatPullbackCompInverseIso a j
  let eJ := J.rightDerivedFunctorPlusSingleIso 0
  let eA := A.rightDerivedFunctorPlusSingleIso 0
  let eJA := JA.rightDerivedFunctorPlusSingleIso 0
  let : IsIso JA.rightDerivedFunctorPlusUnit :=
    JA.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  have he := derivedFlatPullbackCompInverseIso_unit a j K
  have huJA := singleComplexIso_unit JA M
  apply (cancel_epi (JA.rightDerivedFunctorPlusUnit.app K)).mp
  change JA.rightDerivedFunctorPlusUnit.app K ≫
      e.hom.app (DerivedCategory.Plus.Q.obj K) ≫
      A.rightDerivedFunctorPlus.map (eJ.hom.app M) ≫ eA.hom.app (J.obj M) =
    JA.rightDerivedFunctorPlusUnit.app K ≫ eJA.hom.app M ≫
      (DerivedCategory.Plus.singleFunctor U.Modules 0).map
        ((flatPullbackCompInverseIso a j).hom.app M)
  rw [← Category.assoc (JA.rightDerivedFunctorPlusUnit.app K)
    (e.hom.app (DerivedCategory.Plus.Q.obj K)), he]
  simp only [Category.assoc]
  rw [compositeSingleUnit J A M]
  rw [← Category.assoc (JA.rightDerivedFunctorPlusUnit.app K) (eJA.hom.app M), huJA]
  have hn := singleComplexIso_naturality JA (flatPullbackCompInverseIso a j).hom M
  have hQ := congrArg (DerivedCategory.Plus.Q (C := U.Modules)).map hn
  simp only [Functor.map_comp] at hQ
  exact hQ

end DerivedSingle

section Homology

variable {U V X : Scheme.{u}} (a : U ⟶ V) (j : V ⟶ X)
  [Flat a] [Flat j] (n : ℤ)

private def homologyCompLeft :
    (pullback (a ≫ j)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor U.Modules n ⟶
      DerivedCategory.Plus.homologyFunctor X.Modules n ⋙ pullback j ⋙ pullback a :=
  Functor.whiskerRight (derivedFlatPullbackCompInverseIso a j).hom
      (DerivedCategory.Plus.homologyFunctor U.Modules n) ≫
    Functor.whiskerLeft (pullback j).rightDerivedFunctorPlus
      ((pullback a).rightDerivedFunctorPlusHomologyIso n).hom ≫
    Functor.whiskerRight ((pullback j).rightDerivedFunctorPlusHomologyIso n).hom
      (pullback a)

private def homologyCompRight :
    (pullback (a ≫ j)).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.homologyFunctor U.Modules n ⟶
      DerivedCategory.Plus.homologyFunctor X.Modules n ⋙ pullback j ⋙ pullback a :=
  ((pullback (a ≫ j)).rightDerivedFunctorPlusHomologyIso n).hom ≫
    Functor.whiskerLeft (DerivedCategory.Plus.homologyFunctor X.Modules n)
      (flatPullbackCompInverseIso a j).hom

private theorem derivedFlatPullbackCompInverseIso_homology :
    homologyCompLeft a j n = homologyCompRight a j n := by
  apply Localization.natTrans_ext (DerivedCategory.Plus.Q (C := X.Modules))
    (CochainComplex.Plus.quasiIso X.Modules)
  intro K
  dsimp only [homologyCompLeft, homologyCompRight, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  let J := pullback j
  let A := pullback a
  let JA := pullback (a ≫ j)
  let H₀ := DerivedCategory.Plus.homologyFunctor X.Modules n
  let H₁ := DerivedCategory.Plus.homologyFunctor V.Modules n
  let H₂ := DerivedCategory.Plus.homologyFunctor U.Modules n
  let KJ := J.mapCochainComplexPlus.obj K
  let KJA := A.mapCochainComplexPlus.obj KJ
  let K₀ := JA.mapCochainComplexPlus.obj K
  let P := (DerivedCategory.Plus.homologyFunctorFactors (A := X.Modules) n).app K
  let PJ := (DerivedCategory.Plus.homologyFunctorFactors (A := V.Modules) n).app KJ
  let PJA := (DerivedCategory.Plus.homologyFunctorFactors (A := U.Modules) n).app KJA
  let P₀ := (DerivedCategory.Plus.homologyFunctorFactors (A := U.Modules) n).app K₀
  let e := derivedFlatPullbackCompInverseIso a j
  let eJ := J.rightDerivedFunctorPlusHomologyIso n
  let eA := A.rightDerivedFunctorPlusHomologyIso n
  let eJA := JA.rightDerivedFunctorPlusHomologyIso n
  let ξ := (NatIso.mapCochainComplexPlus (flatPullbackCompInverseIso a j)).hom.app K
  let : IsIso JA.rightDerivedFunctorPlusUnit :=
    JA.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  have he := congrArg H₂.map (derivedFlatPullbackCompInverseIso_unit a j K)
  simp only [Functor.map_comp] at he
  have hA := eA.hom.naturality (J.rightDerivedFunctorPlusUnit.app K)
  change H₂.map (A.rightDerivedFunctorPlus.map (J.rightDerivedFunctorPlusUnit.app K)) ≫
      eA.hom.app (J.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) =
    eA.hom.app (DerivedCategory.Plus.Q.obj KJ) ≫
      A.map (H₁.map (J.rightDerivedFunctorPlusUnit.app K)) at hA
  have hJunit := J.rightDerivedFunctorPlusHomologyIso_unit n K
  change H₁.map (J.rightDerivedFunctorPlusUnit.app K) ≫
      eJ.hom.app (DerivedCategory.Plus.Q.obj K) ≫ J.map P.hom =
    PJ.hom ≫ ((K.obj.sc n).mapHomologyIso J).hom at hJunit
  have hAunit := A.rightDerivedFunctorPlusHomologyIso_unit n KJ
  change H₂.map (A.rightDerivedFunctorPlusUnit.app KJ) ≫
      eA.hom.app (DerivedCategory.Plus.Q.obj KJ) ≫ A.map PJ.hom =
    PJA.hom ≫ ((KJ.obj.sc n).mapHomologyIso A).hom at hAunit
  have hJAunit := JA.rightDerivedFunctorPlusHomologyIso_unit n K
  change H₂.map (JA.rightDerivedFunctorPlusUnit.app K) ≫
      eJA.hom.app (DerivedCategory.Plus.Q.obj K) ≫ JA.map P.hom =
    P₀.hom ≫ ((K.obj.sc n).mapHomologyIso JA).hom at hJAunit
  have hξ := (flatPullbackCompInverseIso a j).hom.naturality P.hom
  change JA.map P.hom ≫ (flatPullbackCompInverseIso a j).hom.app (K.obj.homology n) =
    (flatPullbackCompInverseIso a j).hom.app (H₀.obj (DerivedCategory.Plus.Q.obj K)) ≫
      A.map (J.map P.hom) at hξ
  have hSC := NatTrans.app_homology (flatPullbackCompInverseIso a j).hom (K.obj.sc n)
  change (flatPullbackCompInverseIso a j).hom.app (K.obj.homology n) =
    ((K.obj.sc n).mapHomologyIso JA).inv ≫ homologyMap ξ.hom n ≫
      ((K.obj.sc n).mapHomologyIso (J ⋙ A)).hom at hSC
  have hP := (DerivedCategory.Plus.homologyFunctorFactors (A := U.Modules) n).hom.naturality ξ
  change H₂.map (DerivedCategory.Plus.Q.map ξ) ≫ PJA.hom =
    P₀.hom ≫ homologyMap ξ.hom n at hP
  apply (cancel_epi (H₂.map (JA.rightDerivedFunctorPlusUnit.app K))).mp
  apply (cancel_mono (A.map (J.map P.hom))).mp
  simp only [Category.assoc]
  conv_lhs =>
    rw [← Category.assoc (H₂.map (JA.rightDerivedFunctorPlusUnit.app K))
      (H₂.map (e.hom.app (DerivedCategory.Plus.Q.obj K))), he]
    simp only [Category.assoc]
    rw [Functor.rightDerivedFunctorPlusCompUnit_app, Functor.map_comp]
    simp only [Category.assoc]
    rw [← Category.assoc
      (H₂.map (A.rightDerivedFunctorPlus.map (J.rightDerivedFunctorPlusUnit.app K)))
      (eA.hom.app (J.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K))), hA]
    simp only [Category.assoc]
    rw [← A.map_comp (eJ.hom.app (DerivedCategory.Plus.Q.obj K)) (J.map P.hom)]
    rw [← A.map_comp (H₁.map (J.rightDerivedFunctorPlusUnit.app K))
      (eJ.hom.app (DerivedCategory.Plus.Q.obj K) ≫ J.map P.hom)]
    rw [hJunit, A.map_comp]
    rw [← Category.assoc (eA.hom.app (DerivedCategory.Plus.Q.obj KJ)) (A.map PJ.hom)]
    rw [← Category.assoc (H₂.map (A.rightDerivedFunctorPlusUnit.app KJ))
      (eA.hom.app (DerivedCategory.Plus.Q.obj KJ) ≫ A.map PJ.hom), hAunit]
    simp only [Category.assoc]
  conv_rhs =>
    rw [← hξ]
    rw [← Category.assoc (eJA.hom.app (DerivedCategory.Plus.Q.obj K)) (JA.map P.hom)]
    rw [← Category.assoc (H₂.map (JA.rightDerivedFunctorPlusUnit.app K))
      (eJA.hom.app (DerivedCategory.Plus.Q.obj K) ≫ JA.map P.hom), hJAunit]
    simp only [Category.assoc]
    rw [hSC]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc P₀.hom (homologyMap ξ.hom n), ← hP]
    rw [ShortComplex.mapHomologyIso_comp_hom J A (K.obj.sc n)]
    simp only [Category.assoc]
  rfl

end Homology

section HomologyInverse

variable {U V X : Scheme.{u}} (a : U ⟶ V) (j : V ⟶ X)
  [Flat a] [Flat j] (n : ℤ)

private theorem derivedFlatPullbackCompInverseIso_homology_inv
    (K : DerivedCategory.Plus X.Modules) :
    (flatPullbackCompInverseIso a j).inv.app
        ((DerivedCategory.Plus.homologyFunctor X.Modules n).obj K) ≫
        ((pullback (a ≫ j)).rightDerivedFunctorPlusHomologyIso n).inv.app K =
      (pullback a).map
        (((pullback j).rightDerivedFunctorPlusHomologyIso n).inv.app K) ≫
        ((pullback a).rightDerivedFunctorPlusHomologyIso n).inv.app
          ((pullback j).rightDerivedFunctorPlus.obj K) ≫
        (DerivedCategory.Plus.homologyFunctor U.Modules n).map
          ((derivedFlatPullbackCompInverseIso a j).inv.app K) := by
  let J := pullback j
  let A := pullback a
  let JA := pullback (a ≫ j)
  let H₀ := DerivedCategory.Plus.homologyFunctor X.Modules n
  let H₂ := DerivedCategory.Plus.homologyFunctor U.Modules n
  let e := derivedFlatPullbackCompInverseIso a j
  let eJ := J.rightDerivedFunctorPlusHomologyIso n
  let eA := A.rightDerivedFunctorPlusHomologyIso n
  let eJA := JA.rightDerivedFunctorPlusHomologyIso n
  let L := H₂.mapIso (e.app K) ≪≫ eA.app (J.rightDerivedFunctorPlus.obj K) ≪≫ A.mapIso (eJ.app K)
  let R := eJA.app K ≪≫ (flatPullbackCompInverseIso a j).app (H₀.obj K)
  have h := congrArg (fun η => η.app K) (derivedFlatPullbackCompInverseIso_homology a j n)
  change L.hom = R.hom at h
  have hi := congrArg Iso.inv (Iso.ext h : L = R)
  simpa only [L, R, Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] using hi.symm

end HomologyInverse

section HigherModel

variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  [Flat a] [Flat j] (h : IsPullback a b f j)
  (M : U.Modules) (n : ℕ)

private theorem higherFlat_app_model :
    (higherDirectImageFlatBaseChangeMap a b f j h n).app M =
      (pullback j).map (((pushforward f).rightDerivedSingleHomologyIso n).hom.app M) ≫
        ((pullback j).rightDerivedFunctorPlusHomologyIso (n : ℤ)).inv.app
          ((pushforward f).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) ≫
        (DerivedCategory.Plus.homologyFunctor V.Modules (n : ℤ)).map
          ((derivedFlatBaseChangeMap a b f j h).app
            ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M)) ≫
        (DerivedCategory.Plus.homologyFunctor V.Modules (n : ℤ)).map
          ((pushforward b).rightDerivedFunctorPlus.map
            (((pullback a).rightDerivedFunctorPlusSingleIso 0).hom.app M)) ≫
        ((pushforward b).rightDerivedSingleHomologyIso n).inv.app ((pullback a).obj M) := by
  exact higherDirectImageFlatBaseChangeMap_app a b f j h n M

end HigherModel

section HigherPasting

variable {X₀ X₁ X₂ Y₀ Y₁ Y₂ : Scheme.{u}}
  (a : X₁ ⟶ X₀) (b : X₁ ⟶ Y₁) (f : X₀ ⟶ Y₀) (j : Y₁ ⟶ Y₀)
  (c : X₂ ⟶ X₁) (d : X₂ ⟶ Y₂) (v : Y₂ ⟶ Y₁)
  [Flat a] [Flat c] [Flat j] [Flat v]
  (h : IsPullback a b f j) (h' : IsPullback c d b v)
  (H : IsPullback (c ≫ a) d f (v ≫ j)) (M : X₀.Modules) (n : ℕ)

private def derivedLeft :
    (pushforward f).rightDerivedFunctorPlus ⋙
        (pullback j).rightDerivedFunctorPlus ⋙ (pullback v).rightDerivedFunctorPlus ⟶
      (pullback a).rightDerivedFunctorPlus ⋙
        (pullback c).rightDerivedFunctorPlus ⋙ (pushforward d).rightDerivedFunctorPlus :=
  Functor.whiskerLeft (pushforward f).rightDerivedFunctorPlus
      (derivedFlatPullbackCompInverseIso v j).inv ≫
    derivedFlatBaseChangeMap (c ≫ a) d f (v ≫ j) H ≫
    Functor.whiskerRight (derivedFlatPullbackCompInverseIso c a).hom
      (pushforward d).rightDerivedFunctorPlus

private def derivedRight :
    (pushforward f).rightDerivedFunctorPlus ⋙
        (pullback j).rightDerivedFunctorPlus ⋙ (pullback v).rightDerivedFunctorPlus ⟶
      (pullback a).rightDerivedFunctorPlus ⋙
        (pullback c).rightDerivedFunctorPlus ⋙ (pushforward d).rightDerivedFunctorPlus :=
  Functor.whiskerRight (derivedFlatBaseChangeMap a b f j h)
      (pullback v).rightDerivedFunctorPlus ≫
    Functor.whiskerLeft (pullback a).rightDerivedFunctorPlus
      (derivedFlatBaseChangeMap c d b v h')

private theorem derivedFlat_pasting_natTrans :
    derivedLeft a f j c d v H = derivedRight a b f j c d v h h' := by
  apply NatTrans.ext
  funext K
  have he := derivedFlatBaseChangeMap_comp a b f j h c d v h' H K
  change (derivedFlatPullbackPlusCompIso v j).hom.app
      ((pushforward f).rightDerivedFunctorPlus.obj K) ≫
      (derivedFlatBaseChangeMap (c ≫ a) d f (v ≫ j) H).app K =
    (pullback v).rightDerivedFunctorPlus.map
      ((derivedFlatBaseChangeMap a b f j h).app K) ≫
      (derivedFlatBaseChangeMap c d b v h').app
        ((pullback a).rightDerivedFunctorPlus.obj K) ≫
      (pushforward d).rightDerivedFunctorPlus.map
        ((derivedFlatPullbackPlusCompIso c a).hom.app K) at he
  have hi := congrArg (fun t => t ≫ (pushforward d).rightDerivedFunctorPlus.map
      ((derivedFlatPullbackPlusCompIso c a).inv.app K)) he
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] at hi
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hi
  simpa only [derivedLeft, derivedRight, derivedFlatPullbackCompInverseIso,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc] using hi

private def higherPastingPrefix :
    (pullback v).obj ((pullback j).obj (((pushforward f).rightDerived n).obj M)) ⟶
      (DerivedCategory.Plus.homologyFunctor Y₂.Modules (n : ℤ)).obj
        ((pullback v).rightDerivedFunctorPlus.obj
          ((pullback j).rightDerivedFunctorPlus.obj
            ((pushforward f).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor X₀.Modules 0).obj M)))) :=
  (pullback v).map
      ((pullback j).map (((pushforward f).rightDerivedSingleHomologyIso n).hom.app M)) ≫
    (pullback v).map
      (((pullback j).rightDerivedFunctorPlusHomologyIso (n : ℤ)).inv.app
        ((pushforward f).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor X₀.Modules 0).obj M))) ≫
    ((pullback v).rightDerivedFunctorPlusHomologyIso (n : ℤ)).inv.app
      ((pullback j).rightDerivedFunctorPlus.obj
        ((pushforward f).rightDerivedFunctorPlus.obj
          ((DerivedCategory.Plus.singleFunctor X₀.Modules 0).obj M)))

private def higherPastingSuffix :
    (DerivedCategory.Plus.homologyFunctor Y₂.Modules (n : ℤ)).obj
        ((pushforward d).rightDerivedFunctorPlus.obj
          ((pullback c).rightDerivedFunctorPlus.obj
            ((pullback a).rightDerivedFunctorPlus.obj
              ((DerivedCategory.Plus.singleFunctor X₀.Modules 0).obj M)))) ⟶
      ((pushforward d).rightDerived n).obj ((pullback c).obj ((pullback a).obj M)) :=
  (DerivedCategory.Plus.homologyFunctor Y₂.Modules (n : ℤ)).map
      ((pushforward d).rightDerivedFunctorPlus.map
        ((pullback c).rightDerivedFunctorPlus.map
          (((pullback a).rightDerivedFunctorPlusSingleIso 0).hom.app M))) ≫
    (DerivedCategory.Plus.homologyFunctor Y₂.Modules (n : ℤ)).map
      ((pushforward d).rightDerivedFunctorPlus.map
        (((pullback c).rightDerivedFunctorPlusSingleIso 0).hom.app
          ((pullback a).obj M))) ≫
    ((pushforward d).rightDerivedSingleHomologyIso n).inv.app
      ((pullback c).obj ((pullback a).obj M))

private theorem rightHigher_normalization :
    (pullback v).map ((higherDirectImageFlatBaseChangeMap a b f j h n).app M) ≫
        (higherDirectImageFlatBaseChangeMap c d b v h' n).app ((pullback a).obj M) =
      higherPastingPrefix f j v M n ≫
        (DerivedCategory.Plus.homologyFunctor Y₂.Modules (n : ℤ)).map
          ((derivedRight a b f j c d v h h').app
            ((DerivedCategory.Plus.singleFunctor X₀.Modules 0).obj M)) ≫
        higherPastingSuffix a c d M n := by
  let F := pushforward f
  let J := pullback j
  let V := pullback v
  let A := pullback a
  let B := pushforward b
  let C := pullback c
  let D := pushforward d
  let H₁ := DerivedCategory.Plus.homologyFunctor Y₁.Modules (n : ℤ)
  let H₂ := DerivedCategory.Plus.homologyFunctor Y₂.Modules (n : ℤ)
  let K := (DerivedCategory.Plus.singleFunctor X₀.Modules 0).obj M
  let eB := B.rightDerivedSingleHomologyIso n
  let eV := V.rightDerivedFunctorPlusHomologyIso (n : ℤ)
  let sA := (A.rightDerivedFunctorPlusSingleIso 0).hom.app M
  let sC := (C.rightDerivedFunctorPlusSingleIso 0).hom.app (A.obj M)
  let δ₁ := (derivedFlatBaseChangeMap a b f j h).app K
  let δ₂ := (derivedFlatBaseChangeMap c d b v h')
  have hSA := eV.inv.naturality (B.rightDerivedFunctorPlus.map sA)
  change V.map (H₁.map (B.rightDerivedFunctorPlus.map sA)) ≫
      eV.inv.app (B.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X₁.Modules 0).obj (A.obj M))) =
    eV.inv.app (B.rightDerivedFunctorPlus.obj (A.rightDerivedFunctorPlus.obj K)) ≫
      H₂.map (V.rightDerivedFunctorPlus.map (B.rightDerivedFunctorPlus.map sA)) at hSA
  have hδ₁ := eV.inv.naturality δ₁
  change V.map (H₁.map δ₁) ≫
      eV.inv.app (B.rightDerivedFunctorPlus.obj (A.rightDerivedFunctorPlus.obj K)) =
    eV.inv.app (J.rightDerivedFunctorPlus.obj (F.rightDerivedFunctorPlus.obj K)) ≫
      H₂.map (V.rightDerivedFunctorPlus.map δ₁) at hδ₁
  have hδ₂ := δ₂.naturality sA
  change V.rightDerivedFunctorPlus.map (B.rightDerivedFunctorPlus.map sA) ≫
      δ₂.app ((DerivedCategory.Plus.singleFunctor X₁.Modules 0).obj (A.obj M)) =
    δ₂.app (A.rightDerivedFunctorPlus.obj K) ≫
      D.rightDerivedFunctorPlus.map (C.rightDerivedFunctorPlus.map sA) at hδ₂
  rw [higherFlat_app_model a b f j h M n,
    higherFlat_app_model c d b v h' (A.obj M) n]
  simp only [Functor.map_comp, Category.assoc]
  rw [← V.map_comp_assoc (eB.inv.app (A.obj M)) (eB.hom.app (A.obj M)),
    Iso.inv_hom_id_app]
  erw [V.map_id, Category.id_comp]
  rw [← Category.assoc (V.map (H₁.map (B.rightDerivedFunctorPlus.map sA)))
      (eV.inv.app (B.rightDerivedFunctorPlus.obj
        ((DerivedCategory.Plus.singleFunctor X₁.Modules 0).obj (A.obj M)))), hSA]
  simp only [Category.assoc]
  rw [← Category.assoc (V.map (H₁.map δ₁))
      (eV.inv.app (B.rightDerivedFunctorPlus.obj (A.rightDerivedFunctorPlus.obj K))), hδ₁]
  simp only [Category.assoc]
  rw [← H₂.map_comp_assoc
      (V.rightDerivedFunctorPlus.map (B.rightDerivedFunctorPlus.map sA))
      (δ₂.app ((DerivedCategory.Plus.singleFunctor X₁.Modules 0).obj (A.obj M))),
    hδ₂, H₂.map_comp]
  dsimp only [higherPastingPrefix, higherPastingSuffix, derivedRight,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [Functor.map_comp, Category.assoc]
  rfl

private theorem leftHigher_normalization :
    (flatPullbackCompInverseIso v j).inv.app (((pushforward f).rightDerived n).obj M) ≫
        (higherDirectImageFlatBaseChangeMap (c ≫ a) d f (v ≫ j) H n).app M ≫
        ((pushforward d).rightDerived n).map ((flatPullbackCompInverseIso c a).hom.app M) =
      higherPastingPrefix f j v M n ≫
        (DerivedCategory.Plus.homologyFunctor Y₂.Modules (n : ℤ)).map
          ((derivedLeft a f j c d v H).app
            ((DerivedCategory.Plus.singleFunctor X₀.Modules 0).obj M)) ≫
        higherPastingSuffix a c d M n := by
  let F := pushforward f
  let J := pullback j
  let V := pullback v
  let JV := pullback (v ≫ j)
  let A := pullback a
  let C := pullback c
  let AC := pullback (c ≫ a)
  let D := pushforward d
  let H₀ := DerivedCategory.Plus.homologyFunctor Y₀.Modules (n : ℤ)
  let H₂ := DerivedCategory.Plus.homologyFunctor Y₂.Modules (n : ℤ)
  let K := (DerivedCategory.Plus.singleFunctor X₀.Modules 0).obj M
  let eF := F.rightDerivedSingleHomologyIso n
  let eD := D.rightDerivedSingleHomologyIso n
  let eJV := JV.rightDerivedFunctorPlusHomologyIso (n : ℤ)
  let sAC := (AC.rightDerivedFunctorPlusSingleIso 0).hom.app M
  let ξ := (flatPullbackCompInverseIso c a).hom.app M
  have hF := (flatPullbackCompInverseIso v j).inv.naturality (eF.hom.app M)
  change V.map (J.map (eF.hom.app M)) ≫
      (flatPullbackCompInverseIso v j).inv.app (H₀.obj (F.rightDerivedFunctorPlus.obj K)) =
    (flatPullbackCompInverseIso v j).inv.app ((F.rightDerived n).obj M) ≫
      JV.map (eF.hom.app M) at hF
  have hD := eD.inv.naturality ξ
  change H₂.map (D.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.singleFunctor X₂.Modules 0).map ξ)) ≫
      eD.inv.app (C.obj (A.obj M)) =
    eD.inv.app (AC.obj M) ≫ (D.rightDerived n).map ξ at hD
  have hs := derivedFlatPullbackCompInverseIso_single c a M
  rw [higherFlat_app_model (c ≫ a) d f (v ≫ j) H M n]
  simp only [Category.assoc]
  rw [← Category.assoc ((flatPullbackCompInverseIso v j).inv.app ((F.rightDerived n).obj M))
      (JV.map (eF.hom.app M)), ← hF]
  simp only [Category.assoc]
  rw [← Category.assoc
      ((flatPullbackCompInverseIso v j).inv.app (H₀.obj (F.rightDerivedFunctorPlus.obj K)))
      (eJV.inv.app (F.rightDerivedFunctorPlus.obj K)),
    derivedFlatPullbackCompInverseIso_homology_inv v j (n : ℤ) (F.rightDerivedFunctorPlus.obj K)]
  simp only [Category.assoc]
  rw [← hD]
  rw [← H₂.map_comp_assoc (D.rightDerivedFunctorPlus.map sAC)
    (D.rightDerivedFunctorPlus.map ((DerivedCategory.Plus.singleFunctor X₂.Modules 0).map ξ))]
  rw [← D.rightDerivedFunctorPlus.map_comp sAC
    ((DerivedCategory.Plus.singleFunctor X₂.Modules 0).map ξ), ← hs]
  dsimp only [higherPastingPrefix, higherPastingSuffix, derivedLeft,
    NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [Functor.map_comp, Category.assoc]
  rfl

private theorem higherFlat_pasting :
    (flatPullbackCompInverseIso v j).inv.app (((pushforward f).rightDerived n).obj M) ≫
        (higherDirectImageFlatBaseChangeMap (c ≫ a) d f (v ≫ j) H n).app M ≫
        ((pushforward d).rightDerived n).map ((flatPullbackCompInverseIso c a).hom.app M) =
      (pullback v).map ((higherDirectImageFlatBaseChangeMap a b f j h n).app M) ≫
        (higherDirectImageFlatBaseChangeMap c d b v h' n).app ((pullback a).obj M) := by
  rw [leftHigher_normalization, rightHigher_normalization,
    derivedFlat_pasting_natTrans a b f j c d v h h' H]

end HigherPasting

/-- Successive flat changes of base paste for the original higher-direct-image maps,
through the original pullback composition maps, for arbitrary module coefficients. -/
@[reassoc]
theorem higherDirectImageFlatBaseChangeMap_comp
    {W U V X W' V' : Scheme.{u}}
    (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
    (h : IsPullback a b f j) (c : W' ⟶ W) (d : W' ⟶ V') (v : V' ⟶ V)
    (h' : IsPullback c d b v) (H : IsPullback (c ≫ a) d f (v ≫ j))
    [Flat j] [Flat v] (M : U.Modules) (n : ℕ) :
    (pullbackComp v j).hom.app (((pushforward f).rightDerived n).obj M) ≫
        (higherDirectImageFlatBaseChangeMap (c ≫ a) d f (v ≫ j) H n).app M =
      (pullback v).map ((higherDirectImageFlatBaseChangeMap a b f j h n).app M) ≫
        (higherDirectImageFlatBaseChangeMap c d b v h' n).app ((pullback a).obj M) ≫
        ((pushforward d).rightDerived n).map ((pullbackComp c a).hom.app M) := by
  let := flat_cartesian_baseChange a b f j h
  let := flat_cartesian_baseChange c d b v h'
  have he := higherFlat_pasting a b f j c d v h h' H M n
  have hi := congrArg (fun t => t ≫ ((pushforward d).rightDerived n).map
      ((pullbackComp c a).hom.app M)) he
  simp only [flatPullbackCompInverseIso, Iso.symm_hom, Iso.symm_inv, Category.assoc,
    ← Functor.map_comp, Iso.inv_hom_id_app] at hi
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hi
  exact hi

/-- Equal original upper and base arrows transport the original flat higher-image
comparison through the native pullback equality isomorphisms. -/
@[reassoc]
theorem higherDirectImageFlatBaseChangeMap_congr
    {W U V X : Scheme.{u}}
    (a a' : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (g g' : V ⟶ X)
    (h : IsPullback a b f g) (h' : IsPullback a' b f g')
    [Flat g] [Flat g'] (ha : a = a') (hg : g = g') (M : U.Modules) (n : ℕ) :
    (pullbackCongr hg).hom.app (((pushforward f).rightDerived n).obj M) ≫
        (higherDirectImageFlatBaseChangeMap a' b f g' h' n).app M =
      (higherDirectImageFlatBaseChangeMap a b f g h n).app M ≫
        ((pushforward b).rightDerived n).map ((pullbackCongr ha).hom.app M) := by
  subst a'
  subst g'
  simp only [pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

end AlgebraicGeometry.Scheme.Modules
