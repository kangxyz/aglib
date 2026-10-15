/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Functoriality.PullbackPushforward
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.GodementUnit

/-! # The canonical Godement pullback-pushforward unit

Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/ProjectiveLine/P5PositiveUnitAffine.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`e2a5e17578652e168b9679659a38015d6f1a771effbcf83fb8d740b8cd83edfd`.
Selected declarations: positivePlus, positivePlusUnit, positivePlusUnit_app,
  positiveValueDerivedIso, positivePlusUnit_original_comparison, unitOnPlus_isIso_of_quasiIso,
  positivePlusUnit_quasiIso_of_derivedUnit.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules.Godement
/-- The standard derived-category model for module sheaves on `X` in pullback-pushforward
comparisons. -/
local instance generalDerivedStandard (X : Scheme.{u}) :
    HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _

/-- Pull back along `p`, take the Godement total complex, and push forward along `p`. -/
def pullbackPushforwardPlus {P X : Scheme.{u}} (p : P ⟶ X) :
    CochainComplex.Plus X.Modules ⥤ CochainComplex.Plus X.Modules :=
  (Scheme.Modules.pullback p).mapCochainComplexPlus ⋙ godementTotalPlus P ⋙
    (Scheme.Modules.pushforward p).mapCochainComplexPlus

/-- The pullback-pushforward unit followed by pushforward of the Godement total unit. -/
def pullbackPushforwardPlusUnit {P X : Scheme.{u}} (p : P ⟶ X) :
    𝟭 (CochainComplex.Plus X.Modules) ⟶ pullbackPushforwardPlus p :=
  Plus.pullbackPushforwardUnit p ≫ Functor.whiskerRight
    (Functor.whiskerLeft (Scheme.Modules.pullback p).mapCochainComplexPlus
      (godementTotalPlusUnit P)) (Scheme.Modules.pushforward p).mapCochainComplexPlus

lemma pullbackPushforwardPlusUnit_app {P X : Scheme.{u}} (p : P ⟶ X)
    (K : CochainComplex.Plus X.Modules) :
    (pullbackPushforwardPlusUnit p).app K = (Plus.pullbackPushforwardUnit p).app K ≫
      (Scheme.Modules.pushforward p).mapCochainComplexPlus.map
        ((godementTotalPlusUnit P).app
          ((Scheme.Modules.pullback p).mapCochainComplexPlus.obj K)) := rfl

/-- For flat `p`, the comparison from the localized Godement pullback-pushforward complex to the
bounded-below derived composite. -/
def pullbackPushforwardPlusDerivedIso {P X : Scheme.{u}} (p : P ⟶ X) [Flat p]
    (K : CochainComplex.Plus X.Modules) :
    DerivedCategory.Plus.Q.obj ((pullbackPushforwardPlus p).obj K) ≅
      (derivedPullbackPushforwardPlus p).obj (DerivedCategory.Plus.Q.obj K) := by
  have : IsIso (Scheme.Modules.pullback p).rightDerivedFunctorPlusUnit :=
    isIso_derivedFlatPullbackPlusUnit p
  exact (godementTotalDerivedPushforwardIso p).app
      ((Scheme.Modules.pullback p).mapCochainComplexPlus.obj K) ≪≫
    (derivedPushforwardPlus p).mapIso
      (asIso ((Scheme.Modules.pullback p).rightDerivedFunctorPlusUnit.app K))

lemma pullbackPushforwardPlusUnit_derived_comparison {P X : Scheme.{u}} (p : P ⟶ X) [Flat p]
    (K : CochainComplex.Plus X.Modules) :
    DerivedCategory.Plus.Q.map ((pullbackPushforwardPlusUnit p).app K) ≫
        (pullbackPushforwardPlusDerivedIso p K).hom =
      (derivedPullbackPushforwardPlusUnitOnPlus p).app K := by
  dsimp only [pullbackPushforwardPlusDerivedIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    asIso_hom, pullbackPushforwardPlus]
  let C := (Scheme.Modules.pullback p).mapCochainComplexPlus.obj K
  let v := (derivedPushforwardPlus p).map
    ((Scheme.Modules.pullback p).rightDerivedFunctorPlusUnit.app K)
  have hc := godementBaseChange_total_unit_cancel p C
  have he := congrArg (fun q =>
    DerivedCategory.Plus.Q.map ((Plus.pullbackPushforwardUnit p).app K) ≫ q ≫ v) hc
  calc
    _ = DerivedCategory.Plus.Q.map ((Plus.pullbackPushforwardUnit p).app K) ≫
        (DerivedCategory.Plus.Q.map
          ((Scheme.Modules.pushforward p).mapCochainComplexPlus.map
            ((godementTotalPlusUnit P).app C)) ≫
          (godementTotalDerivedPushforwardIso p).hom.app C) ≫ v := by
      rw [pullbackPushforwardPlusUnit_app, Functor.map_comp]
      dsimp only [C, v]
      simp only [Category.assoc]
    _ = DerivedCategory.Plus.Q.map ((Plus.pullbackPushforwardUnit p).app K) ≫
        (derivedPushforwardPlusUnit p).app C ≫ v := he
    _ = _ := rfl

lemma isIso_derivedUnit_of_quasiIso_unit {P X : Scheme.{u}} (p : P ⟶ X) [Flat p]
    (K : CochainComplex.Plus X.Modules) (hK : QuasiIso ((pullbackPushforwardPlusUnit p).app
      K).hom) :
    IsIso ((derivedPullbackPushforwardPlusUnitOnPlus p).app K) := by
  have : IsIso (DerivedCategory.Plus.Q.map ((pullbackPushforwardPlusUnit p).app K)) :=
    Localization.inverts _ (CochainComplex.Plus.quasiIso X.Modules) _ hK
  let e := pullbackPushforwardPlusDerivedIso p K
  have : IsIso e.hom := inferInstance
  rw [← pullbackPushforwardPlusUnit_derived_comparison p K]
  change IsIso (DerivedCategory.Plus.Q.map ((pullbackPushforwardPlusUnit p).app K) ≫ e.hom)
  infer_instance

lemma quasiIso_unit_of_isIso_derivedUnit {P X : Scheme.{u}} (p : P ⟶ X) [Flat p]
    (K : CochainComplex.Plus X.Modules)
    (hK : IsIso ((derivedPullbackPushforwardPlusUnit p).app (DerivedCategory.Plus.Q.obj K))) :
    QuasiIso ((pullbackPushforwardPlusUnit p).app K).hom := by
  have hU : IsIso ((derivedPullbackPushforwardPlusUnitOnPlus p).app K) := by
    rw [← derivedPullbackPushforwardPlusUnit_app p K]
    exact hK
  let e := pullbackPushforwardPlusDerivedIso p K
  have : IsIso e.hom := inferInstance
  have hQ : IsIso (DerivedCategory.Plus.Q.map ((pullbackPushforwardPlusUnit p).app K)) := by
    have h := hU
    rw [← pullbackPushforwardPlusUnit_derived_comparison p K] at h
    change IsIso (DerivedCategory.Plus.Q.map ((pullbackPushforwardPlusUnit p).app K) ≫ e.hom) at h
    exact (isIso_comp_right_iff _ _).mp h
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso X.Modules _).mp
  change IsIso (DerivedCategory.Plus.ι.map
    (DerivedCategory.Plus.Q.map ((pullbackPushforwardPlusUnit p).app K)))
  infer_instance

end AlgebraicGeometry.Scheme.Modules.Godement
