/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ExtResolutionRepresentatives
public import Aglib.CategoryTheory.Sites.PushforwardSections
public import Aglib.CategoryTheory.Sites.SectionsAdditive
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartCycleWitness
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.EtaleTerminalSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramEtaleSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Derived.BaseChangeResolution

/-! # Original higher exchange on arbitrary represented chart classes

The original higher base-change map for a literal étale chart sends every
original represented class to its original chart cohomology class. This is an
all-degree equality of the original maps, not a degree-zero certificate or a
claim that represented classes extend globally. Base, slice and chart Ext
universes remain independent; this ordinary interface needs no derived model.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex Opposite

universe u w s e

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Etale)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over ((siteBaseChange f).obj U))
    AddCommGrpCat.{u + 1})]
  [hChartExt : HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]

local instance baseChangeChartSections_chartObjectHasExt : HasExt.{e}
    (AbelianSheaf.{u, u + 1} ((siteBaseChange f).obj U).left) := hChartExt

local instance baseChangeChartSections_chartIdentitySiteHasExt : HasExt.{e}
    (Sheaf ((𝟭 Scheme.{u}).obj ((siteBaseChange f).obj U).left).smallEtaleTopology
      AddCommGrpCat.{u + 1}) := hChartExt

omit [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over ((siteBaseChange f).obj U))
    AddCommGrpCat.{u + 1})] hChartExt in
/-- The actual ordinary section square, already in the functor-section
heads consumed by the resolution exchange. -/
private theorem originalChartSection_underived
    (M : AbelianSheaf.{u, u + 1} X) :
    let R₁ := directImage f
    let H := inverseImage (pullback.snd U.hom f)
    let ΓU := globalSections U.left
    let α := baseChangeMap f (pullback.fst U.hom f) U.hom
      (pullback.snd U.hom f) pullback.condition
    let e₁ := (siteBaseChange f).sheafPushforwardContinuousSectionsIso
      AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology S)
      (Scheme.smallEtaleTopology X) U
    let e₂ := directImageGlobalSectionsIso (pullback.fst U.hom f)
    let cS := Continuity.pullbackSectionsEtaleEvaluationNatIso U
    let cX := Continuity.pullbackSectionsEtaleEvaluationNatIso ((siteBaseChange f).obj U)
    ΓU.map (α.app M) ≫ e₂.hom.app (H.obj M) ≫ cX.hom.app M =
      cS.hom.app (R₁.obj M) ≫ e₁.hom.app M := by
  dsimp only
  have he₁ := (siteBaseChange f).sheafPushforwardContinuousSectionsIso_hom_app
    AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology S)
      (Scheme.smallEtaleTopology X) U M
  exact (baseChangeMap_etaleEvaluation f U M).trans
    ((congrArg (fun k =>
      (Continuity.pullbackSectionsEtaleEvaluationNatIso U).hom.app
        ((directImage f).obj M) ≫ k) he₁).trans (Category.comp_id _)).symm

omit [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over ((siteBaseChange f).obj U))
    AddCommGrpCat.{u + 1})] hChartExt in
/-- The literal resolution lift on sections, including the original direct-image
section identification, is fixed before representative pairing. -/
private theorem originalChartSection_liftSections
    {F : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution F)
    (J : InjectiveResolution ((inverseImage (pullback.snd U.hom f)).obj F)) (q : ℕ) :
    let H := inverseImage (pullback.snd U.hom f)
    let ΓS := (sheafSections (Scheme.smallEtaleTopology S)
      AddCommGrpCat.{u + 1}).obj (op U)
    let ΓV := globalSections (pullback U.hom f)
    let e₁ := (siteBaseChange f).sheafPushforwardContinuousSectionsIso
      AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology S)
      (Scheme.smallEtaleTopology X) U
    let cX := Continuity.pullbackSectionsEtaleEvaluationNatIso ((siteBaseChange f).obj U)
    let φ := InjectiveResolution.ExactFunctor.lift H I J (𝟙 _)
    let Φ := InjectiveResolution.ExactFunctor.extendedLift H I J φ
    let φPlus := InjectiveResolution.ExactFunctor.liftPlus H I J (𝟙 _)
    ∀ a : ΓS.obj ((directImage f).obj (I.cochainComplex.X (q : ℤ))),
      ΓV.map (Φ.f (q : ℤ))
        ((Continuity.pullbackSectionsEtaleEvaluationIso
          (I.cochainComplex.X (q : ℤ)) ((siteBaseChange f).obj U)).inv a) =
      ΓV.map (φPlus.hom.f (q : ℤ))
        (cX.inv.app (I.cochainComplex.X (q : ℤ))
          (e₁.hom.app (I.cochainComplex.X (q : ℤ)) a)) := by
  dsimp only
  intro a
  have h := ConcreteCategory.congr_hom
    ((siteBaseChange f).sheafPushforwardContinuousSectionsIso_hom_app
      AddCommGrpCat.{u + 1} (Scheme.smallEtaleTopology S)
      (Scheme.smallEtaleTopology X) U (I.cochainComplex.X (q : ℤ))) a
  exact congrArg (fun z =>
    (globalSections (pullback U.hom f)).map
      ((InjectiveResolution.ExactFunctor.extendedLift
        (inverseImage (pullback.snd U.hom f)) I J
        (InjectiveResolution.ExactFunctor.lift
          (inverseImage (pullback.snd U.hom f)) I J (𝟙 _))).f (q : ℤ))
      ((Continuity.pullbackSectionsEtaleEvaluationIso
        (I.cochainComplex.X (q : ℤ)) ((siteBaseChange f).obj U)).inv z)) h.symm

omit [HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over ((siteBaseChange f).obj U))
    AddCommGrpCat.{u + 1})] hChartExt in
/-- Convert the original source witness once from evaluation maps to the
actual native section-functor maps. -/
private theorem originalChartSection_sourceCycle
    {F : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution F) (q : ℕ)
    (a : Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
      (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U) ⟶ I.cocomplex.X q)
    (ha : a ≫ I.cocomplex.d q (q + 1) = 0) :
    let R₁ := directImage f
    let ΓS := (sheafSections (Scheme.smallEtaleTopology S)
      AddCommGrpCat.{u + 1}).obj (op U)
    let K := (R₁.mapHomologicalComplex (.up ℤ)).obj I.cochainComplex
    Functor.CycleWitness
      (fun z => ΓS.map (K.iCycles (q : ℤ)) z)
      (fun z => ΓS.map (K.homologyπ (q : ℤ)) z)
      (Sheaf.Hypercohomology.sectionsEquiv.{u + 1}
        (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U) _
        (a ≫ (I.cochainComplexXIso q q rfl).inv))
      (ΓS.map (I.isoRightDerivedObjCochain R₁ q).hom
        (((resolutionCohomologyToHigherDirectImage f q).app F).app (op U)
          (originalCohomologyResolutionEquiv f U F q
            (I.extMk a (q + 1) rfl ha)))) :=
  originalHigherSection_cycleWitness_extMk f U I q a ha

/-- Convert the original target witness once to the literal fibre-product
cohomology and native section-functor heads. -/
private theorem originalChartSection_targetCycle
    {F : AbelianSheaf.{u, u + 1} X} (I : InjectiveResolution F)
    (J : InjectiveResolution ((inverseImage (pullback.snd U.hom f)).obj F)) (q : ℕ)
    (a : Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
      (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U) ⟶ I.cocomplex.X q)
    (ha : a ≫ I.cocomplex.d q (q + 1) = 0) :
    let R₂ := directImage (pullback.fst U.hom f)
    let H := inverseImage (pullback.snd U.hom f)
    let ΓU := globalSections U.left
    let ΓV := globalSections (pullback U.hom f)
    let e₂ := directImageGlobalSectionsIso (pullback.fst U.hom f)
    let T := (R₂.mapHomologicalComplex (.up ℤ)).obj J.cochainComplex
    let φ := InjectiveResolution.ExactFunctor.lift H I J (𝟙 _)
    let Φ := InjectiveResolution.ExactFunctor.extendedLift H I J φ
    Functor.CycleWitness
      (fun z => e₂.hom.app (J.cochainComplex.X (q : ℤ))
        (ΓU.map (T.iCycles (q : ℤ)) z))
      (fun z => ΓU.map (T.homologyπ (q : ℤ)) z)
      (ΓV.map (Φ.f (q : ℤ))
        ((Continuity.pullbackSectionsEtaleEvaluationIso
          (I.cochainComplex.X (q : ℤ)) ((siteBaseChange f).obj U)).inv
            (Sheaf.Hypercohomology.sectionsEquiv.{u + 1}
              (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U) _
              (a ≫ (I.cochainComplexXIso q q rfl).inv))))
      (ΓU.map (J.isoRightDerivedObjCochain R₂ q).hom
        (cohomologyToHigherSections (pullback.fst U.hom f) (H.obj F) q
          (fibreProductCohomologyEquiv f U F q (I.extMk a (q + 1) rfl ha)))) :=
  originalChartSection_cycleWitness_extMk
    (S' := U.left) ((siteBaseChange f).obj U) (pullback.fst U.hom f) I J q a ha

private theorem originalChartSection_of_resolutionEquation
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (I : InjectiveResolution F)
    (J : InjectiveResolution ((inverseImage (pullback.snd U.hom f)).obj F))
    (b : (inverseImage U.hom).obj (((directImage f).rightDerived q).obj F) ⟶
      ((directImage (pullback.fst U.hom f)).rightDerived q).obj
        ((inverseImage (pullback.snd U.hom f)).obj F))
    (hb : Functor.HigherResolutionExchangeEquation
      (directImage f) (directImage (pullback.fst U.hom f))
      (inverseImage U.hom) (inverseImage (pullback.snd U.hom f))
      (baseChangeMap f (pullback.fst U.hom f) U.hom (pullback.snd U.hom f)
        pullback.condition) I J
      (InjectiveResolution.ExactFunctor.liftPlus (inverseImage (pullback.snd U.hom f))
        I J (𝟙 _)) q b)
    (x : Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (Scheme.smallEtaleTopology X) F q ((siteBaseChange f).obj U)) :
    (globalSections U.left).map b
        ((Continuity.pullbackSectionsEtaleEvaluationIso ((higherDirectImage f q).obj F)
          U).inv
          (((resolutionCohomologyToHigherDirectImage f q).app F).app (op U)
            (originalCohomologyResolutionEquiv f U F q x))) =
      cohomologyToHigherSections (pullback.fst U.hom f)
        ((inverseImage (pullback.snd U.hom f)).obj F) q
        (fibreProductCohomologyEquiv f U F q x) := by
  exact Functor.higherResolutionExchangeEquation_of_extRepresentatives
    (A := AbelianSheaf.{u, u + 1} S) (B := AbelianSheaf.{u, u + 1} X)
    (C := AbelianSheaf.{u, u + 1} U.left)
    (D := AbelianSheaf.{u, u + 1} (pullback U.hom f))
    (directImage f) (directImage (pullback.fst U.hom f))
    (inverseImage U.hom) (inverseImage (pullback.snd U.hom f))
    ((sheafSections (Scheme.smallEtaleTopology S) AddCommGrpCat.{u + 1}).obj (op U))
    ((sheafSections (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
      (op ((siteBaseChange f).obj U)))
    (globalSections U.left) (globalSections (pullback U.hom f))
    (baseChangeMap f (pullback.fst U.hom f) U.hom (pullback.snd U.hom f) pullback.condition)
    ((siteBaseChange f).sheafPushforwardContinuousSectionsIso AddCommGrpCat.{u + 1}
      (Scheme.smallEtaleTopology S) (Scheme.smallEtaleTopology X) U)
    (directImageGlobalSectionsIso (pullback.fst U.hom f))
    (Continuity.pullbackSectionsEtaleEvaluationNatIso U)
    (Continuity.pullbackSectionsEtaleEvaluationNatIso ((siteBaseChange f).obj U))
    (originalChartSection_underived f U) I J
    (InjectiveResolution.ExactFunctor.liftPlus (inverseImage (pullback.snd U.hom f))
      I J (𝟙 _)) q b hb
    (Sheaf.Hypercohomology.freeAbelianSheaf.{u + 1}
      (Scheme.smallEtaleTopology X) ((siteBaseChange f).obj U))
    (fun c => ((resolutionCohomologyToHigherDirectImage f q).app F).app (op U)
      (originalCohomologyResolutionEquiv f U F q c))
    (fun c => cohomologyToHigherSections (pullback.fst U.hom f)
      ((inverseImage (pullback.snd U.hom f)).obj F) q
      (fibreProductCohomologyEquiv f U F q c))
    _ _ (originalChartSection_liftSections f U I J q)
    (originalChartSection_sourceCycle f U I q)
    (originalChartSection_targetCycle f U I J q) x


/-- The original higher exchange on every original represented class is its
original chart cohomology class, followed by the original higher-section map. -/
theorem higherBaseChangeMap_originalChart
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    (x : Sheaf.LargeCohomology.H.{w, u + 1, u, u + 1}
      (Scheme.smallEtaleTopology X) F q ((siteBaseChange f).obj U)) :
    (globalSections U.left).map
        ((higherBaseChangeMap f (pullback.fst U.hom f) U.hom (pullback.snd U.hom f)
          pullback.condition q).app F)
        ((Continuity.pullbackSectionsEtaleEvaluationIso ((higherDirectImage f q).obj F)
          U).inv
          (((resolutionCohomologyToHigherDirectImage f q).app F).app (op U)
            (originalCohomologyResolutionEquiv f U F q x))) =
      cohomologyToHigherSections (pullback.fst U.hom f)
        ((inverseImage (pullback.snd U.hom f)).obj F) q
        (fibreProductCohomologyEquiv f U F q x) :=
  originalChartSection_of_resolutionEquation f U F q (injectiveResolution F)
    (injectiveResolution ((inverseImage (pullback.snd U.hom f)).obj F))
    ((higherBaseChangeMap f (pullback.fst U.hom f) U.hom (pullback.snd U.hom f)
      pullback.condition q).app F)
    (higherBaseChangeMap_resolution_lift f (pullback.fst U.hom f) U.hom
      (pullback.snd U.hom f) pullback.condition (injectiveResolution F)
      (injectiveResolution ((inverseImage (pullback.snd U.hom f)).obj F)) q) x

end AlgebraicGeometry.Scheme.EtaleCohomology
