/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartResolutionSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductCohomology
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GlobalSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.SlicePullback.AugmentationSections

/-! # The original chart augmentation and geometric pullback -/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

private theorem comp_map_id {C D : Type*} [Category* C] [Category* D]
    (R : C ⥤ D) (A : C) {B : D} (f : B ⟶ R.obj A) : f ≫ R.map (𝟙 A) = f :=
  (congrArg (fun k => f ≫ k) (R.map_id A)).trans (Category.comp_id f)

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w s e
attribute [local instance] hasSheafifyLarge

variable {X : Scheme.{u}} (U : X.Etale)

/-- The actual chart comparison followed by the actual represented augmentation is the
original inverse-image constant source. The equality is proved on the same integer generator. -/
theorem chartComparisonSource_augmentation :
    chartComparisonSource U ≫ (inverseImage U.hom).map (representedIntegerAugmentation U) =
      ((inverseImageConstantIso U.hom).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv := by
  let Z := (constantSheaf (Scheme.smallEtaleTopology X) AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ))
  apply (chartHomSectionsEquiv U Z).injective
  have hl := chartComparisonSource_sections_comp U (representedIntegerAugmentation U)
  have ha := representedIntegerAugmentation_sections U Z (𝟙 Z)
  have hp := constantIntegerHomGlobalSectionsIso_pullback U.hom (𝟙 Z)
  have hp' : (constantIntegerHomGlobalSectionsIso U.left).hom.app _
      (((inverseImageConstantIso U.hom).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv) =
      globalSectionsPullback U.hom Z ((constantIntegerHomGlobalSectionsIso X).hom.app Z (𝟙 Z)) :=
    (congrArg ((constantIntegerHomGlobalSectionsIso U.left).hom.app _)
      (comp_map_id (inverseImage U.hom) Z
        (((inverseImageConstantIso U.hom).app
          (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv))).symm.trans hp
  have he := ConcreteCategory.congr_hom
    (Continuity.globalSectionsPullback_etaleEvaluation Z U)
    ((constantIntegerHomGlobalSectionsIso X).hom.app Z (𝟙 Z))
  change (Continuity.pullbackSectionsEtaleEvaluationIso Z U).hom
      ((constantIntegerHomGlobalSectionsIso U.left).hom.app _
        (chartComparisonSource U ≫ (inverseImage U.hom).map (representedIntegerAugmentation U))) =
    (Continuity.pullbackSectionsEtaleEvaluationIso Z U).hom
      ((constantIntegerHomGlobalSectionsIso U.left).hom.app _
        (((inverseImageConstantIso U.hom).app (AddCommGrpCat.of (ULift.{u + 1} ℤ))).inv))
  refine hl.trans ?_
  have ha' : Sheaf.Hypercohomology.sectionsEquiv.{u + 1}
        (Scheme.smallEtaleTopology X) U Z (representedIntegerAugmentation U) =
      Z.obj.map ((etaleTerminalIsTerminal X).from U).op
        ((constantIntegerHomGlobalSectionsIso X).hom.app Z (𝟙 Z)) := by
    exact (congrArg (Sheaf.Hypercohomology.sectionsEquiv.{u + 1}
      (Scheme.smallEtaleTopology X) U Z)
      (Category.comp_id (representedIntegerAugmentation U))).symm.trans ha
  exact ha'.trans (he.symm.trans
    (congrArg (Continuity.pullbackSectionsEtaleEvaluationIso Z U).hom hp'.symm))

variable [hBaseExt : HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over U) AddCommGrpCat.{u + 1})]
  [hChartExt : HasExt.{e} (AbelianSheaf.{u, u + 1} U.left)]

local instance : HasExt.{w}
    (AbelianSheaf.{u, u + 1} ((Functor.fromPUnit X).obj U.right)) := hBaseExt

local instance : HasExt.{e}
    (Sheaf ((𝟭 Scheme.{u}).obj U.left).smallEtaleTopology AddCommGrpCat.{u + 1}) := hChartExt

/-- Original represented restriction followed by the original chart comparison is geometric
pullback in every degree, with the original exact-functor and constant-source maps. -/
theorem originalCohomologyChartEquiv_augmentation
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (c : Sheaf.H.{w} F q) :
    originalCohomologyChartEquiv.{u, w, s, e} U F q
        ((Ext.mk₀ (representedIntegerAugmentation U)).comp c (Nat.zero_add q)) =
      cohomologyPullback.{u, w, e} U.hom F q c := by
  rw [originalCohomologyChartEquiv_apply, cohomologyPullback_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.comp_assoc _ _ _ (Nat.zero_add 0) (Nat.zero_add q) (Nat.zero_add q),
    Ext.mk₀_comp_mk₀, chartComparisonSource_augmentation]

end AlgebraicGeometry.Scheme.EtaleCohomology

namespace AlgebraicGeometry.Scheme.EtaleCohomology

universe u w s e
attribute [local instance] hasSheafifyLarge

variable {X S : Scheme.{u}} (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj (etaleTerminal S))) AddCommGrpCat.{u + 1})]
  [hPullbackExt : HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback (𝟙 S) f))]

local instance : HasExt.{e}
    (AbelianSheaf.{u, u + 1} (pullback (etaleTerminal S).hom f)) := hPullbackExt

local instance : HasExt.{e}
    (AbelianSheaf.{u, u + 1} ((siteBaseChange f).obj (etaleTerminal S)).left) := hPullbackExt

/-- The original global class at the terminal chart is the original geometric pullback class. -/
theorem fibreProductCohomologyEquiv_globalTerminalClass
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (c : Sheaf.H.{w} F q) :
    fibreProductCohomologyEquiv.{u, w, s, e} f (etaleTerminal S) F q
        (globalCohomologyTerminalClass f F q c) =
      cohomologyPullback.{u, w, e} (pullback.snd (𝟙 S) f) F q c := by
  exact originalCohomologyChartEquiv_augmentation
    ((siteBaseChange f).obj (etaleTerminal S)) F q c

end AlgebraicGeometry.Scheme.EtaleCohomology
