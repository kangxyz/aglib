/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Flat
public import Aglib.AlgebraicGeometry.Cohomology.Flasque.DerivedPushforward
public import Aglib.AlgebraicGeometry.Cohomology.Godement.DerivedPushforward.Total

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/GodementBaseChangeUnit.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 154]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Actual ordinary base change followed by Godement total

The chain-level map is the original ordinary cartesian mate followed by the
original total augmentation. Its localization is identified with the installed
derived mate through the original composite units and unit naturality.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
attribute [local instance] Abelian.hasFiniteBiproducts

open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules.Godement
/-- The standard derived-category model for module sheaves on `X` in base-change comparisons. -/
local instance baseChangeSpanStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

variable {W U V X : Scheme.{u}} (a : W ⟶ U) (b : W ⟶ V) (f : U ⟶ X) (j : V ⟶ X)
  (h : IsPullback a b f j) [Flat j] [Flat a]

/-- The original chain-level ordinary mate followed by pushforward of the actual total unit. -/
def godementBaseChangeMap :
    (Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback j).mapCochainComplexPlus ⟶
      (Scheme.Modules.pullback a).mapCochainComplexPlus ⋙ godementTotalPlus W ⋙
        (Scheme.Modules.pushforward b).mapCochainComplexPlus :=
  NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap a b f j h) ≫
    (Functor.mapCochainComplexPlusCompIso (Scheme.Modules.pullback a)
      (Scheme.Modules.pushforward b)).hom ≫
    CategoryTheory.Functor.whiskerLeft (Scheme.Modules.pullback a).mapCochainComplexPlus
      (CategoryTheory.Functor.whiskerRight (godementTotalPlusUnit W)
        (Scheme.Modules.pushforward b).mapCochainComplexPlus)

omit [Flat j] [Flat a] in
/-- Each component is the ordinary mate followed by the original pushforward augmentation. -/
lemma godementBaseChangeMap_app (K : CochainComplex.Plus U.Modules) :
    (godementBaseChangeMap a b f j h).app K =
      (NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap a b f j h)).app K ≫
        (Scheme.Modules.pushforward b).mapCochainComplexPlus.map
          ((godementTotalPlusUnit W).app
            ((Scheme.Modules.pullback a).mapCochainComplexPlus.obj K)) :=
  by simp [godementBaseChangeMap, Functor.mapCochainComplexPlusCompIso]

/-- The actual target comparison uses the installed derived unit and actual total augmentation. -/
def godementBaseChangeTargetIso :
    (Scheme.Modules.pullback a).mapCochainComplexPlus ⋙ godementTotalPlus W ⋙
        (Scheme.Modules.pushforward b).mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q ≅
      DerivedCategory.Plus.Q ⋙ derivedFlatPullbackPlus a ⋙ derivedPushforwardPlus b := by
  let : IsIso (Scheme.Modules.pullback a).rightDerivedFunctorPlusUnit :=
    isIso_derivedFlatPullbackPlusUnit a
  exact Functor.isoWhiskerLeft (Scheme.Modules.pullback a).mapCochainComplexPlus
      (godementTotalDerivedPushforwardIso b) ≪≫
    Functor.isoWhiskerRight (asIso (Scheme.Modules.pullback a).rightDerivedFunctorPlusUnit)
      (derivedPushforwardPlus b)

/-- The two original comparison factors of the target isomorphism. -/
lemma godementBaseChangeTargetIso_hom_factor (K : CochainComplex.Plus U.Modules) :
    (godementBaseChangeTargetIso a b).hom.app K =
      (godementTotalDerivedPushforwardIso b).hom.app
          ((Scheme.Modules.pullback a).mapCochainComplexPlus.obj K) ≫
        (derivedPushforwardPlus b).map
          ((Scheme.Modules.pullback a).rightDerivedFunctorPlusUnit.app K) := rfl

/-- The target comparison retains its precise original units and actual total augmentation. -/
lemma godementBaseChangeTargetIso_hom_app (K : CochainComplex.Plus U.Modules) :
    (godementBaseChangeTargetIso a b).hom.app K =
      (godementTotalDerivedUnit b).app ((Scheme.Modules.pullback a).mapCochainComplexPlus.obj K) ≫
        (asIso (godementTotalDerivedAugmentation b)).inv.app
          ((Scheme.Modules.pullback a).mapCochainComplexPlus.obj K) ≫
        (derivedPushforwardPlus b).map
          ((Scheme.Modules.pullback a).rightDerivedFunctorPlusUnit.app K) := by
  change (_ ≫ _) ≫ _ = _ ≫ _ ≫ _
  exact Category.assoc _ _ _

/-- Original derived-unit naturality cancels the actual total augmentation. -/
lemma godementBaseChange_total_unit_cancel (K : CochainComplex.Plus W.Modules) :
    DerivedCategory.Plus.Q.map ((Scheme.Modules.pushforward b).mapCochainComplexPlus.map
        ((godementTotalPlusUnit W).app K)) ≫
      (godementTotalDerivedPushforwardIso b).hom.app K =
        (derivedPushforwardPlusUnit b).app K := by
  change DerivedCategory.Plus.Q.map ((Scheme.Modules.pushforward b).mapCochainComplexPlus.map
      ((godementTotalPlusUnit W).app K)) ≫
    ((derivedPushforwardPlusUnit b).app ((godementTotalPlus W).obj K) ≫
      (asIso (godementTotalDerivedAugmentation b)).inv.app K) = _
  have hn := (derivedPushforwardPlusUnit b).naturality ((godementTotalPlusUnit W).app K)
  change DerivedCategory.Plus.Q.map ((Scheme.Modules.pushforward b).mapCochainComplexPlus.map
      ((godementTotalPlusUnit W).app K)) ≫
    (derivedPushforwardPlusUnit b).app ((godementTotalPlus W).obj K) =
    (derivedPushforwardPlusUnit b).app K ≫ (derivedPushforwardPlus b).map
      (DerivedCategory.Plus.Q.map ((godementTotalPlusUnit W).app K)) at hn
  rw [← Category.assoc, hn]
  change ((derivedPushforwardPlusUnit b).app K ≫
    (asIso (godementTotalDerivedAugmentation b)).hom.app K) ≫
      (asIso (godementTotalDerivedAugmentation b)).inv.app K = _
  rw [Category.assoc, Iso.hom_inv_id_app]
  exact Category.comp_id _

/-- The Q-image is the ORIGINAL installed derived mate through the original composite units. -/
lemma godementBaseChangeMap_original_unit (K : CochainComplex.Plus U.Modules) :
    DerivedCategory.Plus.Q.map ((godementBaseChangeMap a b f j h).app K) ≫
        (godementBaseChangeTargetIso a b).hom.app K =
      (Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pushforward f)
        (Scheme.Modules.pullback j)).app K ≫
          (derivedFlatBaseChangeMap a b f j h).app (DerivedCategory.Plus.Q.obj K) := by
  let P := (Scheme.Modules.pullback a).mapCochainComplexPlus.obj K
  let t := (NatTrans.mapCochainComplexPlus (cartesianBaseChangeMap a b f j h)).app K
  let z := (Scheme.Modules.pushforward b).mapCochainComplexPlus.map
    ((godementTotalPlusUnit W).app P)
  let v := (derivedPushforwardPlus b).map
    ((Scheme.Modules.pullback a).rightDerivedFunctorPlusUnit.app K)
  have hc := godementBaseChange_total_unit_cancel b P
  have he := congrArg (fun q => DerivedCategory.Plus.Q.map t ≫ q ≫ v) hc
  have hu := derivedFlatBaseChangeMap_unit a b f j h K
  rw [Functor.rightDerivedFunctorPlusCompUnit_app (Scheme.Modules.pullback a)
    (Scheme.Modules.pushforward b) K] at hu
  calc
    _ = (DerivedCategory.Plus.Q.map t ≫ DerivedCategory.Plus.Q.map z) ≫
        ((godementTotalDerivedPushforwardIso b).hom.app P ≫ v) := by
      rw [godementBaseChangeMap_app, Functor.map_comp, godementBaseChangeTargetIso_hom_factor]
    _ = DerivedCategory.Plus.Q.map t ≫
        (DerivedCategory.Plus.Q.map z ≫ (godementTotalDerivedPushforwardIso b).hom.app P) ≫ v :=
      by simp only [Category.assoc]
    _ = DerivedCategory.Plus.Q.map t ≫ (derivedPushforwardPlusUnit b).app P ≫ v := he
    _ = _ := hu.symm

/-- The original source composite derived unit is invertible on actual flasque terms. -/
lemma isIso_baseChangeSourceUnit_of_flasque (K : CochainComplex.Plus U.Modules)
    (hK : ∀ n, TopCat.Presheaf.IsFlasque (K.obj.X n).presheaf) :
    IsIso ((Functor.rightDerivedFunctorPlusCompUnit (Scheme.Modules.pushforward f)
      (Scheme.Modules.pullback j)).app K) := by
  rw [Functor.rightDerivedFunctorPlusCompUnit_app]
  have : IsIso ((Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnit.app K) :=
    isIso_derivedPushforwardPlusUnit_of_flasque f K hK
  have : IsIso (Scheme.Modules.pullback j).rightDerivedFunctorPlusUnit :=
    isIso_derivedFlatPullbackPlusUnit j
  have : IsIso ((Scheme.Modules.pullback j).rightDerivedFunctorPlusUnit.app
      ((Scheme.Modules.pushforward f).mapCochainComplexPlus.obj K)) := inferInstance
  have : IsIso ((Scheme.Modules.pullback j).rightDerivedFunctorPlus.map
      ((Scheme.Modules.pushforward f).rightDerivedFunctorPlusUnit.app K)) := inferInstance
  infer_instance

end AlgebraicGeometry.Scheme.Modules.Godement
