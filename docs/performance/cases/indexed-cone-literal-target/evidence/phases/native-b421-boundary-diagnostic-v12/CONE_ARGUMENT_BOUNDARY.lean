/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramTestRelativeCone
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramTestOuterSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramConeExtension
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramRawConeSections
public import Aglib.CategoryTheory.Limits.NaturalTransformationMapValues

/-! # The original test-row comparison to evaluated limit coefficients -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge
variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (F : DiagramCoefficientSystem X) (c : Cocone X) (i : I)
  (T : (X.obj i).unop.Etale)

/-- Original square maps on the native limit test scheme, without coefficient-map rewriting. -/
def diagramTestRawConeSectionsFunctor : Under i ⥤ AddCommGrpCat.{u + 1} :=
  Under.forget i ⋙ coneOriginalSectionsFunctor X F (diagramTestExtendedCone X c i T)

/-- The whole original section comparison, with literal square maps in its source. -/
def diagramTestConeSectionsComparison :
    diagramTestRawConeSectionsFunctor X F c i T ≅
      diagramTestConeSectionsFunctor X F c i T :=
  Functor.isoWhiskerLeft (Under.forget i)
    (coneOriginalSectionsIso X F (diagramTestExtendedCone X c i T)) ≪≫
  Functor.isoWhiskerLeft (Under.forget i)
    (coneCoefficientEtaleSectionsIso X c F (diagramEtaleTestLimitChart X i T c))

/-- Original base-change evaluation on the fixed limit test chart. -/
def diagramTestConeSectionsIso (a : Under i) :
    (globalSections (diagramTestExtendedCone X c i T).pt.unop).obj
        ((inverseImage (diagramTestConeSchemeMap X c i T a)).obj (F.obj a.right)) ≅
      (diagramTestConeSectionsFunctor X F c i T).obj a :=
  (diagramTestConeSectionsComparison X F c i T).app a

lemma diagramTestConeSectionsIso_hom (a : Under i) :
    (diagramTestConeSectionsIso X F c i T a).hom =
      (pullbackSectionsBaseEtaleIso (c.ι.app a.right).unop (F.obj a.right)).hom.app
        (op (diagramEtaleTestLimitChart X i T c)) := by
  change 𝟙 _ ≫ (coneCoefficientEtaleSectionsIso X c F
    (diagramEtaleTestLimitChart X i T c)).hom.app a.right = _
  exact (Category.id_comp _).trans
    (coneCoefficientEtaleSectionsIso_hom_app X c F (diagramEtaleTestLimitChart X i T c) a.right)

/-- Normalize the actual square using the original cocone extended to the limit chart. -/
lemma diagramTestConeSystemSectionsMap_eq {a b : Under i} (m : a ⟶ b) :
    diagramTestConeSystemSectionsMap X F c i T m =
      (globalSections (diagramTestExtendedCone X c i T).pt.unop).map
        (coneCoefficientMap X
          (diagramTestExtendedCone X c i T) F m.right) :=
  coneSystemSectionsMap_eq X F (diagramTestExtendedCone X c i T) m.right

/- Diagnostic only: one sequential decomposition of the actual failing
whole constructor, retaining its original data and native setup/options. -/
theorem w12DiagComponentFormation
    (_app : ∀ a : Arrow (Under i),
      (diagramTestArrowSectionsFunctor X F i T).obj a ⟶
        (Arrow.leftFunc ⋙ diagramTestRawConeSectionsFunctor X F c i T).obj a) : True :=
  True.intro

def w12DiagComponent : ∀ a : Arrow (Under i),
    (diagramTestArrowSectionsFunctor X F i T).obj a ⟶
      (Arrow.leftFunc ⋙ diagramTestRawConeSectionsFunctor X F c i T).obj a :=
  diagramTestConeArrowSectionsMap X F c i T

theorem w12DiagTargetMapFormation
    (_map : ∀ {a b : Arrow (Under i)}, (a ⟶ b) →
      ((Arrow.leftFunc ⋙ diagramTestRawConeSectionsFunctor X F c i T).obj a ⟶
        (Arrow.leftFunc ⋙ diagramTestRawConeSectionsFunctor X F c i T).obj b)) : True :=
  True.intro

def w12DiagTargetMap {a b : Arrow (Under i)} (m : a ⟶ b) :
    (Arrow.leftFunc ⋙ diagramTestRawConeSectionsFunctor X F c i T).obj a ⟶
      (Arrow.leftFunc ⋙ diagramTestRawConeSectionsFunctor X F c i T).obj b :=
  diagramTestConeSystemSectionsMap X F c i T m.left

theorem w12DiagSquareFormation {a b : Arrow (Under i)} (m : a ⟶ b)
    (_h : (diagramTestArrowSectionsFunctor X F i T).map m ≫
      w12DiagComponent X F c i T b =
        w12DiagComponent X F c i T a ≫ w12DiagTargetMap X F c i T m) : True :=
  True.intro

theorem w12DiagSquare {a b : Arrow (Under i)} (m : a ⟶ b) :
    (diagramTestArrowSectionsFunctor X F i T).map m ≫ w12DiagComponent X F c i T b =
      w12DiagComponent X F c i T a ≫ w12DiagTargetMap X F c i T m :=
  diagramTestConeArrowSectionsMap_naturality X F c i T m

theorem w12DiagMapValueFormation {a b : Arrow (Under i)} (m : a ⟶ b)
    (_h : w12DiagTargetMap X F c i T m =
      (Arrow.leftFunc ⋙ diagramTestRawConeSectionsFunctor X F c i T).map m) : True :=
  True.intro

theorem w12DiagMapValue {a b : Arrow (Under i)} (m : a ⟶ b) :
    w12DiagTargetMap X F c i T m =
      (Arrow.leftFunc ⋙ diagramTestRawConeSectionsFunctor X F c i T).map m :=
  diagramTestConeSystemSectionsMap_eq X F c i T m.left

def w12DiagWhole :
    diagramTestArrowSectionsFunctor X F i T ⟶
      Arrow.leftFunc ⋙ diagramTestRawConeSectionsFunctor X F c i T :=
  NatTrans.ofMapValues (diagramTestArrowSectionsFunctor X F i T)
    (Arrow.leftFunc ⋙ diagramTestRawConeSectionsFunctor X F c i T)
    (w12DiagComponent X F c i T)
    (fun m => w12DiagTargetMap X F c i T m)
    (fun m => w12DiagSquare X F c i T m)
    (fun m => w12DiagMapValue X F c i T m)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
