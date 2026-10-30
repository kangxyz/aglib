/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.SectionComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.Etale
public import Aglib.CategoryTheory.Sites.Point.SectionValues

/-! # Original chart exchange on section groups

The native chart map, its exact original-factor equation and invertibility
theorem project one proof-bearing witness. The witness is constructed from the
original chart-evaluation isomorphism and original higher-exchange component.
All four derived-model data records remain arbitrary and explicit.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite

universe u dX dS dZU dU

namespace AlgebraicGeometry.Scheme.EtaleCohomology

attribute [local instance] hasSheafifyLarge

/-- Form the original chart factors before specializing the coefficient functors. -/
private structure ChartSectionMapWitness {X S : Scheme.{u}} (U : S.Etale)
    (P : AbelianSheaf.{u, u + 1} X ⥤ AbelianSheaf.{u, u + 1} S)
    (Q : AbelianSheaf.{u, u + 1} X ⥤ AbelianSheaf.{u, u + 1} U.left)
    (α : P ⋙ @inverseImage.{u} S U.left U.hom ⟶ Q)
    (F : AbelianSheaf.{u, u + 1} X) where
  map : (P.obj F).obj.obj (op U) ⟶ (globalSections U.left).obj (Q.obj F)
  isIso : IsIso map
  map_eq_family : map = (Continuity.chartSectionComparison U P Q α).app F


-- Apply injectivity before contextual value laws simplify the constructor arguments.
attribute [simp↓] ChartSectionMapWitness.mk.injEq

/-- Construct the original evaluation and exchange component while their family is variable. -/
private def chartSectionMapWitnessOfIsIso {X S : Scheme.{u}} (U : S.Etale)
    (P : AbelianSheaf.{u, u + 1} X ⥤ AbelianSheaf.{u, u + 1} S)
    (Q : AbelianSheaf.{u, u + 1} X ⥤ AbelianSheaf.{u, u + 1} U.left)
    (α : P ⋙ @inverseImage.{u} S U.left U.hom ⟶ Q) (hα : IsIso α)
    (F : AbelianSheaf.{u, u + 1} X) : ChartSectionMapWitness U P Q α F where
  map := (Continuity.chartSectionComparison U P Q α).app F
  isIso := by
    rw [Continuity.chartSectionComparison_app]
    exact chartSectionMapOfHom_isIso (globalSections U.left)
      (@Continuity.pullbackSectionsEtaleEvaluationIso.{u} S (P.obj F) U) (α.app F)
      (by let := hα; infer_instance)
  map_eq_family := rfl


variable {X S : Scheme.{u}} (f : X ⟶ S) (U : S.Etale)
  [hSourceDerived : HasDerivedCategory.{dX} (AbelianSheaf.{u, u + 1} X)]
  [hTargetDerived : HasDerivedCategory.{dS} (AbelianSheaf.{u, u + 1} S)]
  [hChartDerived : HasDerivedCategory.{dZU} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  [hBase : HasDerivedCategory.{dU} (AbelianSheaf.{u, u + 1} U.left)]

/-- The supplied chart-base derived model at the identity presentation of its scheme. -/
local instance chartExchangeMapsBaseIdentityDerived : HasDerivedCategory.{dU}
    (AbelianSheaf.{u, u + 1} ((𝟭 Scheme.{u}).obj U.left)) := hBase

/-- Specialize the original whole exchange before projecting its section map and laws. -/
private opaque originalChartSectionWitness
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    ChartSectionMapWitness U
      (@higherDirectImage.{u} X S f q)
      ((@inverseImage.{u} X (pullback U.hom f) (pullback.snd U.hom f)) ⋙
        @higherDirectImage.{u} (pullback U.hom f) U.left (pullback.fst U.hom f) q)
      (@higherBaseChangeMapFromDerived.{u, dX, dS, dZU, dU} X S (pullback U.hom f) U.left
        hSourceDerived hTargetDerived hChartDerived hBase f (pullback.fst U.hom f)
        U.hom (pullback.snd U.hom f) pullback.condition q) F :=
  chartSectionMapWitnessOfIsIso U
    (@higherDirectImage.{u} X S f q)
    ((@inverseImage.{u} X (pullback U.hom f) (pullback.snd U.hom f)) ⋙
      @higherDirectImage.{u} (pullback U.hom f) U.left (pullback.fst U.hom f) q)
    (@higherBaseChangeMapFromDerived.{u, dX, dS, dZU, dU} X S (pullback U.hom f) U.left
      hSourceDerived hTargetDerived hChartDerived hBase f (pullback.fst U.hom f)
      U.hom (pullback.snd U.hom f) pullback.condition q)
    (by simpa only [higherBaseChangeMapFromDerived_eq] using
      (@higherBaseChangeMap_etale_isIso.{u} X S U.left f U.hom U.prop q)) F

/-- The original chart evaluation followed by its original higher exchange. -/
@[no_expose]
def fibreProductChartSectionMap (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    ((higherDirectImage f q).obj F).obj.obj (op U) ⟶
      (globalSections U.left).obj ((higherDirectImage (pullback.fst U.hom f) q).obj
        ((inverseImage (pullback.snd U.hom f)).obj F)) :=
  (originalChartSectionWitness.{u, dX, dS, dZU, dU} f U
    (hSourceDerived := hSourceDerived) (hTargetDerived := hTargetDerived)
    (hChartDerived := hChartDerived) (hBase := hBase) F q).map

/-- The native map is a component of the same whole chart comparison family. -/
theorem fibreProductChartSectionMap_eq_family
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    fibreProductChartSectionMap.{u, dX, dS, dZU, dU} f U
        (hSourceDerived := hSourceDerived) (hTargetDerived := hTargetDerived)
        (hChartDerived := hChartDerived) (hBase := hBase) F q =
      (Continuity.chartSectionComparison U (higherDirectImage f q)
        (inverseImage (pullback.snd U.hom f) ⋙ higherDirectImage (pullback.fst U.hom f) q)
        (@higherBaseChangeMapFromDerived.{u, dX, dS, dZU, dU} X S (pullback U.hom f) U.left
          hSourceDerived hTargetDerived hChartDerived hBase f (pullback.fst U.hom f)
          U.hom (pullback.snd U.hom f) pullback.condition q)).app F :=
  (originalChartSectionWitness.{u, dX, dS, dZU, dU} f U
    (hSourceDerived := hSourceDerived) (hTargetDerived := hTargetDerived)
    (hChartDerived := hChartDerived) (hBase := hBase) F q).map_eq_family

/-- The native map uses the same actual constructor as its generic section laws. -/
theorem fibreProductChartSectionMap_eq_constructor
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    fibreProductChartSectionMap.{u, dX, dS, dZU, dU} f U
        (hSourceDerived := hSourceDerived) (hTargetDerived := hTargetDerived)
        (hChartDerived := hChartDerived) (hBase := hBase) F q =
      chartSectionMapOfHom (globalSections U.left)
        (Continuity.pullbackSectionsEtaleEvaluationIso ((higherDirectImage f q).obj F) U)
        ((@higherBaseChangeMapFromDerived.{u, dX, dS, dZU, dU} X S (pullback U.hom f) U.left
          hSourceDerived hTargetDerived hChartDerived hBase f (pullback.fst U.hom f)
          U.hom (pullback.snd U.hom f) pullback.condition q).app F) := by
  rw [fibreProductChartSectionMap_eq_family]
  exact Continuity.chartSectionComparison_app U _ _ _ F

/-- The native constructor retains the exact original evaluation and model-dependent exchange. -/
theorem fibreProductChartSectionMap_eq_original
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    fibreProductChartSectionMap.{u, dX, dS, dZU, dU} f U
        (hSourceDerived := hSourceDerived) (hTargetDerived := hTargetDerived)
        (hChartDerived := hChartDerived) (hBase := hBase) F q =
      (Continuity.pullbackSectionsEtaleEvaluationIso ((higherDirectImage f q).obj F) U).inv ≫
        (globalSections U.left).map
          ((@higherBaseChangeMapFromDerived.{u, dX, dS, dZU, dU} X S (pullback U.hom f) U.left
            hSourceDerived hTargetDerived hChartDerived hBase f (pullback.fst U.hom f)
            U.hom (pullback.snd U.hom f) pullback.condition q).app F) :=
  fibreProductChartSectionMap_eq_constructor f U F q

/-- The original chart section map is invertible for arbitrary coefficient sheaves. -/
theorem fibreProductChartSectionMap_isIso
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) :
    IsIso (fibreProductChartSectionMap.{u, dX, dS, dZU, dU} f U
      (hSourceDerived := hSourceDerived) (hTargetDerived := hTargetDerived)
      (hChartDerived := hChartDerived) (hBase := hBase) F q) :=
  (originalChartSectionWitness.{u, dX, dS, dZU, dU} f U
    (hSourceDerived := hSourceDerived) (hTargetDerived := hTargetDerived)
    (hChartDerived := hChartDerived) (hBase := hBase) F q).isIso

end AlgebraicGeometry.Scheme.EtaleCohomology
