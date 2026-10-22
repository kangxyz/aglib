/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.FormalPushforwardComparison
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineCompletionCoordinates
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.PushforwardSpecSections
public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.Completion
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.GlobalSections
public import Aglib.Algebra.Category.ModuleCat.FunctorTransport
public import Aglib.RingTheory.AdicCompletion.Ext

/-! # The original affine proper-pushforward comparison on inverse limits

The ambient upstairs quotient-section tower is not assumed compatible.
Formal functions identifies its actual limit with completion of the original
pushforward's sections. The original quotient units specify the comparison.
-/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules.Coherent
universe u
variable {B : CommRingCat.{u}} [IsNoetherianRing B]
  {Y : Scheme.{u}} [IsLocallyNoetherian Y]
  (p : Y ⟶ Spec B) [IsProper p] (J : Ideal B) (G : Y.CoherentSheaf)

local instance : G.obj.IsQuasicoherent :=
  QuasiCoherent.quasicoherent_of_affineCharts _ (fun R j _ => (G.property R j).1)

/-- Actual Spec sections of the ambient pushforward completion diagram. -/
abbrev affinePushforwardCompletionTower : ℕᵒᵖ ⥤ ModuleCat.{u} B :=
  idealSheafQuotientTower Y (idealThickeningIdealSheaf p J) G.obj ⋙
    pushforward p ⋙ moduleSpecΓFunctor

/-- Whisker and reassociate a whole original-unit comparison before specialization. -/
def whiskerOriginalUnitComparison
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : ℕᵒᵖ ⥤ C) (T : ℕᵒᵖ ⥤ D) (P : D ⥤ C) (R : C ⥤ E)
    (U : C) (u : ∀ n, U ⟶ F.obj (op n)) (v : ∀ n, U ⟶ P.obj (T.obj (op n)))
    (c : {ψ : F ⟶ T ⋙ P // ∀ n, u n ≫ ψ.app (op n) = v n}) :
    {α : F ⋙ R ⟶ T ⋙ P ⋙ R //
      ∀ n, R.map (u n) ≫ α.app (op n) = R.map (v n)} := by
  refine ⟨Functor.whiskerRight c.val R ≫ (Functor.associator T P R).hom, ?_⟩
  intro n
  change R.map (u n) ≫ (R.map (c.val.app (op n)) ≫ 𝟙 _) = _
  rw [Category.comp_id, ← R.map_comp, c.property]

/-- Normalize the whole original affine comparison and its unit certificate together. -/
def affinePushforwardComparisonData :
    {α : ((completionFunctor (Spec B) (idealThickeningIdealSheaf (𝟙 (Spec B)) J)).obj
      (properPushforwardCoefficient p G)).affineSectionsTower ⟶
        affinePushforwardCompletionTower p J G //
      ∀ n, moduleSpecΓFunctor.map
        ((idealSheafQuotientUnit (Spec B) (idealThickeningIdealSheaf (𝟙 (Spec B)) J ^ n)).app
          ((pushforward p).obj G.obj)) ≫ α.app (op n) =
        moduleSpecΓFunctor.map ((pushforward p).map
          ((idealSheafQuotientUnit Y (idealThickeningIdealSheaf p J ^ n)).app G.obj))} := by
  have c := whiskerOriginalUnitComparison
    (idealSheafQuotientTower (Spec B) (idealThickeningIdealSheaf (𝟙 (Spec B)) J)
      ((pushforward p).obj G.obj))
    (idealSheafQuotientTower Y (idealThickeningIdealSheaf (p ≫ 𝟙 (Spec B)) J) G.obj)
    (pushforward p) moduleSpecΓFunctor ((pushforward p).obj G.obj)
    (fun n => (idealSheafQuotientUnit (Spec B)
      (idealThickeningIdealSheaf (𝟙 (Spec B)) J ^ n)).app ((pushforward p).obj G.obj))
    (fun n => (pushforward p).map
      ((idealSheafQuotientUnit Y (idealThickeningIdealSheaf (p ≫ 𝟙 (Spec B)) J ^ n)).app G.obj))
    (formalPushforwardComparisonData p (𝟙 (Spec B)) J G)
  change {α : idealSheafQuotientTower (Spec B) (idealThickeningIdealSheaf (𝟙 (Spec B)) J)
      ((pushforward p).obj G.obj) ⋙ moduleSpecΓFunctor ⟶
        idealSheafQuotientTower Y (idealThickeningIdealSheaf p J) G.obj ⋙
          pushforward p ⋙ moduleSpecΓFunctor //
      ∀ n, moduleSpecΓFunctor.map
        ((idealSheafQuotientUnit (Spec B) (idealThickeningIdealSheaf (𝟙 (Spec B)) J ^ n)).app
          ((pushforward p).obj G.obj)) ≫ α.app (op n) =
        moduleSpecΓFunctor.map ((pushforward p).map
          ((idealSheafQuotientUnit Y (idealThickeningIdealSheaf p J ^ n)).app G.obj))}
  exact Eq.mp (congrArg (fun q : Y ⟶ Spec B =>
    {α : idealSheafQuotientTower (Spec B) (idealThickeningIdealSheaf (𝟙 (Spec B)) J)
        ((pushforward p).obj G.obj) ⋙ moduleSpecΓFunctor ⟶
          idealSheafQuotientTower Y (idealThickeningIdealSheaf q J) G.obj ⋙
            pushforward p ⋙ moduleSpecΓFunctor //
        ∀ n, moduleSpecΓFunctor.map
          ((idealSheafQuotientUnit (Spec B) (idealThickeningIdealSheaf (𝟙 (Spec B)) J ^ n)).app
            ((pushforward p).obj G.obj)) ≫ α.app (op n) =
          moduleSpecΓFunctor.map ((pushforward p).map
            ((idealSheafQuotientUnit Y (idealThickeningIdealSheaf q J ^ n)).app G.obj))})
    (Category.comp_id p)) c

/-- The identity-base specialization, normalized only by the category identity law. -/
def affinePushforwardComparison :
    ((completionFunctor (Spec B) (idealThickeningIdealSheaf (𝟙 (Spec B)) J)).obj
      (properPushforwardCoefficient p G)).affineSectionsTower ⟶
        affinePushforwardCompletionTower p J G :=
  (affinePushforwardComparisonData p J G).val

/-- Literal pointwise original-unit equation, with all carriers kept abstract. -/
def originalUnitValue {R : Type*} [Ring R] {M N P : ModuleCat R}
    (u : M ⟶ N) (a : N ⟶ P) (v : M ⟶ P) (x : M) : Prop := a (u x) = v x

private theorem originalUnitValue_of_comp {R : Type*} [Ring R] {M N P : ModuleCat R}
    (u : M ⟶ N) (a : N ⟶ P) (v : M ⟶ P) (x : M) (h : u ≫ a = v) :
    originalUnitValue u a v x := ConcreteCategory.congr_hom h x

/-- The normalized affine comparison retains the original quotient unit.
The predicate is literally evaluation of the original unit followed by the map. -/
theorem affinePushforwardComparison_unit (n : ℕ)
    (x : moduleSpecΓFunctor.obj ((pushforward p).obj G.obj)) :
    originalUnitValue
      (moduleSpecΓFunctor.map ((idealSheafQuotientUnit (Spec B)
        (idealThickeningIdealSheaf (𝟙 (Spec B)) J ^ n)).app ((pushforward p).obj G.obj)))
      ((affinePushforwardComparison p J G).app (op n))
      (moduleSpecΓFunctor.map ((pushforward p).map
        ((idealSheafQuotientUnit Y (idealThickeningIdealSheaf p J ^ n)).app G.obj))) x :=
  originalUnitValue_of_comp _ _ _ x ((affinePushforwardComparisonData p J G).property n)

/-- Original geometric quotients and the actual structural-section tower agree. -/
def affinePushforwardQuotientTowerIso :
    affinePushforwardCompletionTower p J G ≅
      Cohomology.idealPowerQuotientGlobalSections Y (Cohomology.affineFormalFunctionsScalar p)
        G.obj J :=
  Functor.isoWhiskerRight (Cohomology.idealPowerQuotientIdealSheafTowerIso p J G.obj).symm
    (pushforward p ⋙ moduleSpecΓFunctor) ≪≫
      Functor.isoWhiskerLeft (Cohomology.idealPowerQuotientFunctor Y
        (idealThickeningBaseScalar p) G.obj J) (Cohomology.pushforwardSpecSectionsIso p)

/-- The induced equivalence is coordinatewise on original compatible sections. -/
def affinePushforwardQuotientSectionsEquiv :
    ModuleCat.sectionsSubmodule (affinePushforwardCompletionTower p J G) ≃ₗ[B]
      ModuleCat.sectionsSubmodule
        (Cohomology.idealPowerQuotientGlobalSections Y
          (Cohomology.affineFormalFunctionsScalar p) G.obj J) :=
  ModuleCat.sectionsSubmoduleCongr (affinePushforwardQuotientTowerIso p J G)

/-- Formal functions for the actual proper pushforward's original affine module. -/
def affinePushforwardFormalFunctionsEquiv :
    AdicCompletion J (moduleSpecΓFunctor.obj ((pushforward p).obj G.obj)) ≃ₗ[B]
      ModuleCat.sectionsSubmodule (affinePushforwardCompletionTower p J G) :=
  ((AdicCompletion.congr J
    ((Cohomology.pushforwardSpecSectionsIso p).app G.obj).toLinearEquiv).restrictScalars B).trans
      ((Cohomology.moduleGlobalSectionsFormalFunctionsEquiv G.obj J p G.property).trans
        (affinePushforwardQuotientSectionsEquiv p J G).symm)

/-- On original elements the equivalence is exactly the original quotient reduction. -/
theorem affinePushforwardFormalFunctionsEquiv_of
    (x : moduleSpecΓFunctor.obj ((pushforward p).obj G.obj)) (n : ℕ) :
    ((affinePushforwardQuotientSectionsEquiv p J G)
      (affinePushforwardFormalFunctionsEquiv p J G (AdicCompletion.of J _ x))).val (op n) =
      (idealQuotientπ Y (idealThickeningBaseScalar p) G.obj (J ^ n)).app ⊤
        ((Cohomology.pushforwardSpecSectionsIso p).hom.app G.obj x) := by
  change ((affinePushforwardQuotientSectionsEquiv p J G)
    ((affinePushforwardQuotientSectionsEquiv p J G).symm
      (Cohomology.moduleGlobalSectionsFormalFunctionsEquiv G.obj J p G.property
        (AdicCompletion.map J
          ((Cohomology.pushforwardSpecSectionsIso p).app G.obj).toLinearEquiv.toLinearMap
          (AdicCompletion.of J _ x))))).val (op n) = _
  rw [LinearEquiv.apply_symm_apply, AdicCompletion.map_of]
  exact Cohomology.moduleGlobalSectionsFormalFunctionsEquiv_of G.obj J p G.property _ n

end AlgebraicGeometry.Scheme.Modules.Coherent
