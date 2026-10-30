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
public import Aglib.CategoryTheory.Filtered.IndexedConeSections

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

/- Diagnostic only: decompose the current indexed constructor arguments,
then distinguish its inferred result from the original literal native target. -/
def w12ICLegs :
    Arrow.rightFunc ⋙ diagramEtaleTest X i T ⟶
      (Functor.const (Arrow (Under i))).obj (diagramTestExtendedCone X c i T).pt :=
  Functor.whiskerLeft Arrow.rightFunc (diagramEtaleTestCocone X i T c).ι

theorem w12ICLegTriangle (a : Arrow (Under i)) :
    (diagramTestArrowProjection X i T).app a ≫ (w12ICLegs X c i T).app a =
      (diagramTestExtendedCone X c i T).ι.app a.left.right :=
  congrArg Quiver.Hom.op (diagramTestConeArrowTriangle X c i T a)

def w12ICChosenTriangle {j k : I} (a : j ⟶ k) :
    schemeAdjunctionData.left ((diagramTestExtendedCone X c i T).ι.app j) ≅
      schemeAdjunctionData.left (X.map a) ⋙
        schemeAdjunctionData.left ((diagramTestExtendedCone X c i T).ι.app k) :=
  (diagramConeAdjunctionData X (diagramTestExtendedCone X c i T)).leftTriangle a

theorem w12ICMate {j k : I} (a : j ⟶ k) :
    conjugateEquiv
      ((schemeAdjunctionData.adj (X.map a)).comp
        (schemeAdjunctionData.adj ((diagramTestExtendedCone X c i T).ι.app k)))
      (schemeAdjunctionData.adj ((diagramTestExtendedCone X c i T).ι.app j))
      (w12ICChosenTriangle X c i T a).hom =
        (InjectiveSystem.AdjunctionData.Cone.coconeRightTriangle schemeAdjunctionData
          X (diagramTestExtendedCone X c i T) a).hom :=
  (diagramConeAdjunctionData X (diagramTestExtendedCone X c i T)).conjugate a

def w12ICSourceMap {a b : Arrow (Under i)} (m : a ⟶ b) :
    schemeSectionData.indexedObj X F (Arrow.leftFunc ⋙ Under.forget i)
        (Arrow.rightFunc ⋙ diagramEtaleTest X i T) (diagramTestArrowProjection X i T) a ⟶
      schemeSectionData.indexedObj X F (Arrow.leftFunc ⋙ Under.forget i)
        (Arrow.rightFunc ⋙ diagramEtaleTest X i T) (diagramTestArrowProjection X i T) b :=
  diagramTestArrowSectionsMap X F i T m

theorem w12ICSourceValue {a b : Arrow (Under i)} (m : a ⟶ b) :
    w12ICSourceMap X F i T m =
      schemeSectionData.indexedMap X F (Arrow.leftFunc ⋙ Under.forget i)
        (Arrow.rightFunc ⋙ diagramEtaleTest X i T) (diagramTestArrowProjection X i T) m :=
  diagramTestArrowSectionsMap_eq_generic X F i T m

def w12ICRowApp (a : Arrow (Under i)) :
    schemeSectionData.indexedObj X F (Arrow.leftFunc ⋙ Under.forget i)
        (Arrow.rightFunc ⋙ diagramEtaleTest X i T) (diagramTestArrowProjection X i T) a ⟶
      (schemeSectionData.value (diagramTestExtendedCone X c i T).pt).obj
        ((schemeAdjunctionData.left
          ((diagramTestExtendedCone X c i T).ι.app a.left.right)).obj (F.obj a.left.right)) :=
  diagramTestConeArrowSectionsMap X F c i T a

theorem w12ICRowValue (a : Arrow (Under i)) :
    w12ICRowApp X F c i T a =
      schemeSectionData.indexedConeMap X F (Arrow.leftFunc ⋙ Under.forget i)
        (Arrow.rightFunc ⋙ diagramEtaleTest X i T) (diagramTestArrowProjection X i T)
        (diagramTestExtendedCone X c i T) (w12ICLegs X c i T)
        (w12ICLegTriangle X c i T) a :=
  systemSquareSectionsMap_eq_sectionSystemSquareMap X F (𝟙 a.left.right)
    (diagramTestArrowSchemeMap X i T a) (diagramTestConeSchemeMap X c i T a.left)
    ((diagramEtaleTestCocone X i T c).ι.app a.right).unop
    (diagramTestConeArrowSquare X c i T a)

def w12ICInferred :=
  schemeSectionData.indexedConeNatTransWithMap schemeAdjunctionData_coherent X F
    (Arrow.leftFunc ⋙ Under.forget i) (Arrow.rightFunc ⋙ diagramEtaleTest X i T)
    (diagramTestArrowProjection X i T) (diagramTestExtendedCone X c i T)
    (w12ICLegs X c i T) (w12ICLegTriangle X c i T)
    (fun a => w12ICChosenTriangle X c i T a) (fun a => w12ICMate X c i T a)
    (fun m => w12ICSourceMap X F i T m) (fun m => w12ICSourceValue X F i T m)
    (w12ICRowApp X F c i T) (w12ICRowValue X F c i T)

theorem w12ICNativeTypeFormation
    (_α : diagramTestArrowSectionsFunctor X F i T ⟶
      Arrow.leftFunc ⋙ diagramTestRawConeSectionsFunctor X F c i T) : True := True.intro

def w12ICNativeTarget :
    diagramTestArrowSectionsFunctor X F i T ⟶
      Arrow.leftFunc ⋙ diagramTestRawConeSectionsFunctor X F c i T :=
  w12ICInferred X F c i T

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
