/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.ComparisonPasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramEtaleSections

/-! # Whole section comparisons on base-changed etale charts

The actual unit, evaluation and coefficient-square maps define comparison
families before any higher-direct-image or coefficient component is supplied.
Their component laws retain the original maps. The section square uses a whole
coefficient equation and imposes no invertibility condition on that equation.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u vC uC

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

attribute [local instance] hasSheafifyLarge

private theorem squareSectionsNatTrans_arrow_congr {X S Y T : Scheme.{u}}
    (f : X ⟶ S) (fT : Y ⟶ T) (g : T ⟶ S) (r₁ r₂ : Y ⟶ X)
    (h₁ : fT ≫ g = r₁ ≫ f) (h₂ : fT ≫ g = r₂ ≫ f) (hr : r₁ = r₂) :
    squareSectionsNatTrans f fT g r₁ h₁ =
      squareSectionsNatTrans f fT g r₂ h₂ := by
  subst r₂
  rfl

/-- The identity restriction uses the original first projection of the chart. -/
theorem unitRepresentativeArrow_identity {S T : Scheme.{u}}
    (g : T ⟶ S) (U : S.Etale) :
    (unitRepresentativeArrow g (𝟙 ((siteBaseChange g).obj U))).left =
      pullback.fst U.hom g := by
  let V : T.Etale := (siteBaseChange g).obj U
  let b : V.left ⟶ U.left := pullback.fst U.hom g
  exact (congrArg (fun k : V.left ⟶ V.left => k ≫ b)
    (etaleHom_id_left V)).trans (Category.id_comp b)

/-- At identity restriction the original section map is the original unit component. -/
theorem unitSectionMap_identity {S T : Scheme.{u}}
    (g : T ⟶ S) (U : S.Etale) (L : AbelianSheaf.{u, u + 1} S) :
    unitSectionMap g L (𝟙 ((siteBaseChange g).obj U)) =
      ((inverseImageAdjunction g).unit.app L).hom.app (op U) := by
  let V : T.Etale := (siteBaseChange g).obj U
  let P := ((inverseImage g).obj L).obj
  let a := ((inverseImageAdjunction g).unit.app L).hom.app (op U)
  have hid : P.map (𝟙 V).op = 𝟙 (P.obj (op V)) := by
    simpa only [op_id] using P.map_id (op V)
  change a ≫ P.map (𝟙 V).op = a
  exact (congrArg (fun k => a ≫ k) hid).trans (Category.comp_id a)

/-- The whole original unit square on the actual base-changed chart. -/
theorem unitSectionNatTrans_baseChangeChart_square {S T : Scheme.{u}}
    (g : T ⟶ S) (U : S.Etale) :
    unitSectionNatTrans g (𝟙 ((siteBaseChange g).obj U)) ≫
        Functor.whiskerLeft (inverseImage g)
          (pullbackSectionsEtaleEvaluationNatIso ((siteBaseChange g).obj U)).inv =
      (pullbackSectionsEtaleEvaluationNatIso U).inv ≫
        squareSectionsNatTrans U.hom ((siteBaseChange g).obj U).hom g
          (pullback.fst U.hom g) pullback.condition.symm := by
  let V : T.Etale := (siteBaseChange g).obj U
  let b : V.left ⟶ U.left := pullback.fst U.hom g
  let a := unitRepresentativeArrow g (𝟙 V)
  have hs := squareSectionsNatTrans_arrow_congr U.hom V.hom g a.left b
    (Over.w a).symm pullback.condition.symm (unitRepresentativeArrow_identity g U)
  exact (unitSectionNatTrans_square g (𝟙 V)).trans
    (congrArg (fun t => (pullbackSectionsEtaleEvaluationNatIso U).inv ≫ t) hs)

/-- The same original whole unit law, with its functor associators displayed. -/
theorem unitSectionNatTrans_baseChangeChart_pasting {S T : Scheme.{u}}
    (g : T ⟶ S) (U : S.Etale) :
    unitSectionNatTrans g (𝟙 ((siteBaseChange g).obj U)) ≫
        Functor.whiskerLeft (inverseImage g)
          (pullbackSectionsEtaleEvaluationNatIso ((siteBaseChange g).obj U)).inv ≫
        (Functor.associator (inverseImage g)
          (inverseImage ((siteBaseChange g).obj U).hom)
          (globalSections ((siteBaseChange g).obj U).left)).inv =
      (pullbackSectionsEtaleEvaluationNatIso U).inv ≫
        Functor.whiskerLeft (inverseImage U.hom)
          (globalSectionsPullbackNatTrans (pullback.fst U.hom g)) ≫
        (Functor.associator (inverseImage U.hom) (inverseImage (pullback.fst U.hom g))
          (globalSections ((siteBaseChange g).obj U).left)).inv ≫
        Functor.whiskerRight
          (inverseImageSquareIso U.hom ((siteBaseChange g).obj U).hom g
            (pullback.fst U.hom g) pullback.condition.symm).inv
          (globalSections ((siteBaseChange g).obj U).left) := by
  exact Functor.comparisonPasting_unit_coherence_of_square
    (unitSectionNatTrans g (𝟙 ((siteBaseChange g).obj U)))
    (globalSectionsPullbackNatTrans (pullback.fst U.hom g))
    (pullbackSectionsEtaleEvaluationNatIso U)
    (pullbackSectionsEtaleEvaluationNatIso ((siteBaseChange g).obj U))
    (inverseImageSquareIso U.hom ((siteBaseChange g).obj U).hom g
      (pullback.fst U.hom g) pullback.condition.symm).inv
    (unitSectionNatTrans_baseChangeChart_square g U)

variable {C : Type uC} [Category.{vC} C]

/-- Inverse original chart evaluation followed by an actual coefficient family. -/
def chartSectionComparison {S : Scheme.{u}} (U : S.Etale)
    (P : C ⥤ AbelianSheaf.{u, u + 1} S)
    (Q : C ⥤ AbelianSheaf.{u, u + 1} U.left)
    (α : P ⋙ inverseImage U.hom ⟶ Q) :
    P ⋙ (sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U) ⟶
      Q ⋙ globalSections U.left :=
  Functor.comparisonPasting (pullbackSectionsEtaleEvaluationNatIso U).inv α

/-- The family retains exactly the original evaluation and coefficient component. -/
theorem chartSectionComparison_app {S : Scheme.{u}} (U : S.Etale)
    (P : C ⥤ AbelianSheaf.{u, u + 1} S)
    (Q : C ⥤ AbelianSheaf.{u, u + 1} U.left)
    (α : P ⋙ inverseImage U.hom ⟶ Q) (F : C) :
    (chartSectionComparison U P Q α).app F =
      (pullbackSectionsEtaleEvaluationIso (P.obj F) U).inv ≫
        (globalSections U.left).map (α.app F) :=
  Functor.comparisonPasting_app (pullbackSectionsEtaleEvaluationNatIso U).inv α F

/-- The original unit-and-coefficient section map as a whole family. -/
def unitSectionComparison {S T : Scheme.{u}} (g : T ⟶ S) (U : S.Etale)
    (P : C ⥤ AbelianSheaf.{u, u + 1} S)
    (Q : C ⥤ AbelianSheaf.{u, u + 1} T)
    (α : P ⋙ inverseImage g ⟶ Q) :
    P ⋙ (sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op U) ⟶
      Q ⋙ (sheafSections T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (op ((siteBaseChange g).obj U)) :=
  Functor.comparisonPasting (unitSectionNatTrans g (𝟙 ((siteBaseChange g).obj U))) α

/-- The shared unit family retains the original raw adjunction unit and coefficient map. -/
theorem unitSectionComparison_app {S T : Scheme.{u}} (g : T ⟶ S) (U : S.Etale)
    (P : C ⥤ AbelianSheaf.{u, u + 1} S)
    (Q : C ⥤ AbelianSheaf.{u, u + 1} T)
    (α : P ⋙ inverseImage g ⟶ Q) (F : C) :
    (unitSectionComparison g U P Q α).app F =
      ((inverseImageAdjunction g).unit.app (P.obj F)).hom.app (op U) ≫
        (α.app F).hom.app (op ((siteBaseChange g).obj U)) := by
  exact (Functor.comparisonPasting_app
    (unitSectionNatTrans g (𝟙 ((siteBaseChange g).obj U))) α F).trans
      (congrArg (fun k => k ≫ (α.app F).hom.app (op ((siteBaseChange g).obj U)))
        ((unitSectionNatTrans_app g (𝟙 ((siteBaseChange g).obj U)) (P.obj F)).trans
          (unitSectionMap_identity g U (P.obj F))))

section Square

variable {S T : Scheme.{u}} (g : T ⟶ S) (U : S.Etale)
  (P : C ⥤ AbelianSheaf.{u, u + 1} S)
  (L : C ⥤ AbelianSheaf.{u, u + 1} T)
  (QU : C ⥤ AbelianSheaf.{u, u + 1} U.left)
  (QV : C ⥤ AbelianSheaf.{u, u + 1} ((siteBaseChange g).obj U).left)
  (β : P ⋙ inverseImage g ⟶ L)
  (βU : P ⋙ inverseImage U.hom ⟶ QU)
  (βV : L ⋙ inverseImage ((siteBaseChange g).obj U).hom ⟶ QV)
  (ρ : QU ⋙ inverseImage (pullback.fst U.hom g) ⟶ QV)

/-- The whole coefficient equation gives the square of the same actual section families. -/
theorem sectionComparison_commSq
    (hcoeff : Functor.whiskerLeft P
          (inverseImageSquareIso U.hom ((siteBaseChange g).obj U).hom g
            (pullback.fst U.hom g) pullback.condition.symm).inv ≫
        (Functor.associator P (inverseImage g)
          (inverseImage ((siteBaseChange g).obj U).hom)).inv ≫
        Functor.whiskerRight β (inverseImage ((siteBaseChange g).obj U).hom) ≫ βV =
      (Functor.associator P (inverseImage U.hom)
        (inverseImage (pullback.fst U.hom g))).inv ≫
        Functor.whiskerRight βU (inverseImage (pullback.fst U.hom g)) ≫ ρ) :
    CommSq (unitSectionComparison g U P L β)
      (chartSectionComparison U P QU βU)
      (chartSectionComparison ((siteBaseChange g).obj U) L QV βV)
      (Functor.comparisonPasting
        (globalSectionsPullbackNatTrans (pullback.fst U.hom g)) ρ) :=
  Functor.comparisonPasting_commSq
    (unitSectionNatTrans g (𝟙 ((siteBaseChange g).obj U)))
    (globalSectionsPullbackNatTrans (pullback.fst U.hom g))
    (pullbackSectionsEtaleEvaluationNatIso U)
    (pullbackSectionsEtaleEvaluationNatIso ((siteBaseChange g).obj U)) β βU βV ρ
    (inverseImageSquareIso U.hom ((siteBaseChange g).obj U).hom g
      (pullback.fst U.hom g) pullback.condition.symm).inv
    (unitSectionNatTrans_baseChangeChart_pasting g U) hcoeff

end Square

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
