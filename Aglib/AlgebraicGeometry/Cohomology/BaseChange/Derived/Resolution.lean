/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Flat
public import Aglib.AlgebraicGeometry.Modules.Complex.Basic
public import Aglib.Algebra.Homology.DerivedCategory.KInjective.ExactResolution.Unit
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.SingleHomology

/-!
# Actual resolution maps for the installed derived flat base-change comparison

The original ordinary cartesian mate on a supplied injective resolution
is followed by actual pushforward of the native exact-pullback resolution
comparison. The source and target use the installed derived units and
original resolution augmentations. No quasicoherence or finiteness is
needed for these constructions. The flatness of the pulled-back leg follows
from the supplied cartesian square and flat base map when these maps are
used for base change.
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
local instance flatResolutionStandard (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (h : IsPullback a b f j) [Flat a] [Flat j]
  (M : U.Modules) (I : InjectiveResolution M)
  (J : InjectiveResolution ((pullback a).obj M))

/-- The actual chain map is the original ordinary mate followed by actual pushforward of the
native exact-image resolution comparison. No image quasi-isomorphism is assumed. -/
def flatBaseChangeResolutionMapPlus :
    (pushforward f ⋙ pullback j).mapCochainComplexPlus.obj I.cochainComplexPlus ⟶
      (pushforward b).mapCochainComplexPlus.obj J.cochainComplexPlus :=
  (NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap a b f j h)).app I.cochainComplexPlus ≫
    (pushforward b).mapCochainComplexPlus.map
      (InjectiveResolution.mapCochainComparisonPlus (pullback a) I J)

omit [Flat j] in
/-- Every component is the original ordinary cartesian mate and original chosen resolution
comparison component, with the actual geometric pushforward. -/
theorem flatBaseChangeResolutionMapPlus_hom_f (i : ℤ) :
    (flatBaseChangeResolutionMapPlus a b f j h M I J).hom.f i =
      (cartesianBaseChangeMap a b f j h).app (I.cochainComplex.X i) ≫
        (pushforward b).map
          ((InjectiveResolution.mapCochainComparison (pullback a) I J).f i) := rfl

/-- The original source model is the exact flat-pullback unit followed by the original
right-derived resolution comparison for pushforward. -/
def flatBaseChangeResolutionSourceIso :
    DerivedCategory.Plus.Q.obj
        ((pushforward f ⋙ pullback j).mapCochainComplexPlus.obj I.cochainComplexPlus) ≅
      ((pushforward f).rightDerivedFunctorPlus ⋙ (pullback j).rightDerivedFunctorPlus).obj
        ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M) := by
  letI : IsIso (pullback j).rightDerivedFunctorPlusUnit := isIso_derivedFlatPullbackPlusUnit j
  exact asIso ((pullback j).rightDerivedFunctorPlusUnit.app
      ((pushforward f).mapCochainComplexPlus.obj I.cochainComplexPlus)) ≪≫
    (pullback j).rightDerivedFunctorPlus.mapIso (I.rightDerivedFunctorPlusIso (pushforward f))

/-- The original target model is the native pushforward resolution comparison and the inverse
native exact-pullback/single comparison. -/
def flatBaseChangeResolutionTargetIso :
    DerivedCategory.Plus.Q.obj ((pushforward b).mapCochainComplexPlus.obj J.cochainComplexPlus) ≅
      ((pullback a).rightDerivedFunctorPlus ⋙ (pushforward b).rightDerivedFunctorPlus).obj
        ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M) :=
  J.rightDerivedFunctorPlusIso (pushforward b) ≪≫
    (pushforward b).rightDerivedFunctorPlus.mapIso
      (((pullback a).rightDerivedFunctorPlusSingleIso 0).app M).symm

omit [Flat j] in
private theorem flatPullbackSingleIso_inv_map_resolution :
    ((pullback a).rightDerivedFunctorPlusSingleIso 0).inv.app M ≫
        (pullback a).rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map I.ιPlus) =
      DerivedCategory.Plus.Q.map
          (InjectiveResolution.mapCochainAugmentationPlus (pullback a) I) ≫
        (pullback a).rightDerivedFunctorPlusUnit.app I.cochainComplexPlus := by
  let A := pullback a
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

omit [Flat a] in
private theorem flatBaseChangeResolutionSourceIso_hom_comp :
    (flatBaseChangeResolutionSourceIso f j M I).hom ≫
        ((pushforward f).rightDerivedFunctorPlus ⋙
          (pullback j).rightDerivedFunctorPlus).map (DerivedCategory.Plus.Q.map I.ιPlus) =
      (Functor.rightDerivedFunctorPlusCompUnit (pushforward f) (pullback j)).app
        I.cochainComplexPlus := by
  simp only [flatBaseChangeResolutionSourceIso, Iso.trans_hom, asIso_hom,
    Functor.mapIso_hom, Functor.comp_map, Category.assoc]
  rw [← Functor.map_comp, InjectiveResolution.rightDerivedFunctorPlusIso_hom_comp]
  exact ((pushforward f).rightDerivedFunctorPlusCompUnit_app (pullback j)
    I.cochainComplexPlus).symm

omit [Flat j] in
private theorem flatBaseChangeResolutionTargetIso_hom_comp :
    (flatBaseChangeResolutionTargetIso a b M J).hom ≫
        ((pullback a).rightDerivedFunctorPlus ⋙
          (pushforward b).rightDerivedFunctorPlus).map (DerivedCategory.Plus.Q.map I.ιPlus) =
      (J.rightDerivedFunctorPlusIso (pushforward b)).hom ≫
        (pushforward b).rightDerivedFunctorPlus.map
          (DerivedCategory.Plus.Q.map
            (InjectiveResolution.mapCochainAugmentationPlus (pullback a) I)) ≫
        (pushforward b).rightDerivedFunctorPlus.map
          ((pullback a).rightDerivedFunctorPlusUnit.app I.cochainComplexPlus) := by
  simp only [flatBaseChangeResolutionTargetIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.symm_hom, Iso.app_inv, Functor.comp_map, Category.assoc]
  rw [← Functor.map_comp, flatPullbackSingleIso_inv_map_resolution,
    Functor.map_comp]

/-- The actual chain map represents the original installed derived flat base-change map on
the coefficient single, through its original source and target resolution comparisons. -/
theorem flatBaseChangeResolutionMapPlus_derived :
    DerivedCategory.Plus.Q.map (flatBaseChangeResolutionMapPlus a b f j h M I J) ≫
        (flatBaseChangeResolutionTargetIso a b M J).hom =
      (flatBaseChangeResolutionSourceIso f j M I).hom ≫
        (derivedFlatBaseChangeMap a b f j h).app
          ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M) := by
  let ν := ((pullback a).rightDerivedFunctorPlus ⋙
    (pushforward b).rightDerivedFunctorPlus).map (DerivedCategory.Plus.Q.map I.ιPlus)
  let : IsIso ν := by
    dsimp only [ν]
    infer_instance
  apply (cancel_mono ν).mp
  have hn := (derivedFlatBaseChangeMap a b f j h).naturality
    (DerivedCategory.Plus.Q.map I.ιPlus)
  change ((pushforward f).rightDerivedFunctorPlus ⋙
        (pullback j).rightDerivedFunctorPlus).map (DerivedCategory.Plus.Q.map I.ιPlus) ≫
      (derivedFlatBaseChangeMap a b f j h).app
        (DerivedCategory.Plus.Q.obj I.cochainComplexPlus) =
    (derivedFlatBaseChangeMap a b f j h).app
        ((DerivedCategory.Plus.singleFunctor U.Modules 0).obj M) ≫ ν at hn
  have hs := flatBaseChangeResolutionSourceIso_hom_comp f j M I
  have ht := flatBaseChangeResolutionTargetIso_hom_comp a b M I J
  have hq := InjectiveResolution.mapCochainComparison_rightDerivedUnit
    (pullback a) I J (pushforward b)
  have hq' := congrArg (fun z => z ≫ (pushforward b).rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Q.map
        (InjectiveResolution.mapCochainAugmentationPlus (pullback a) I)) ≫
    (pushforward b).rightDerivedFunctorPlus.map
      ((pullback a).rightDerivedFunctorPlusUnit.app I.cochainComplexPlus)) hq
  simp only [Category.assoc] at hq'
  have hm : DerivedCategory.Plus.Q.map
        (flatBaseChangeResolutionMapPlus a b f j h M I J) ≫
      (flatBaseChangeResolutionTargetIso a b M J).hom ≫ ν =
    DerivedCategory.Plus.Q.map
        ((NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap a b f j h)).app
          I.cochainComplexPlus) ≫
      (Functor.rightDerivedFunctorPlusCompUnit (pullback a) (pushforward b)).app
        I.cochainComplexPlus := by
    dsimp only [ν]
    rw [ht]
    rw [flatBaseChangeResolutionMapPlus, Functor.map_comp]
    simp only [Category.assoc]
    rw [hq', Functor.map_inv, IsIso.inv_hom_id_assoc,
      ← Functor.rightDerivedFunctorPlusCompUnit_app]
  calc
    _ = DerivedCategory.Plus.Q.map
        ((NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap a b f j h)).app
          I.cochainComplexPlus) ≫
          (Functor.rightDerivedFunctorPlusCompUnit (pullback a) (pushforward b)).app
            I.cochainComplexPlus := by simpa only [Category.assoc] using hm
    _ = (Functor.rightDerivedFunctorPlusCompUnit (pushforward f) (pullback j)).app
        I.cochainComplexPlus ≫ (derivedFlatBaseChangeMap a b f j h).app
          (DerivedCategory.Plus.Q.obj I.cochainComplexPlus) :=
      (derivedFlatBaseChangeMap_unit a b f j h I.cochainComplexPlus).symm
    _ = _ := by rw [← hs, Category.assoc, hn, ← Category.assoc]

end AlgebraicGeometry.Scheme.Modules
