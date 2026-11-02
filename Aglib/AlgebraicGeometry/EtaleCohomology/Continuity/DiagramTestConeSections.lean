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

/-- The original relative row maps, assembled before applying the whole chart comparison. -/
def diagramTestRawConeSectionsNatTrans :
    diagramTestArrowSectionsFunctor X F i T ⟶
      Arrow.leftFunc ⋙ diagramTestRawConeSectionsFunctor X F c i T :=
  let row := schemeSectionData.indexedConeNatTransWithMap schemeAdjunctionData_coherent X F
    (Arrow.leftFunc ⋙ Under.forget i) (Arrow.rightFunc ⋙ diagramEtaleTest X i T)
    (diagramTestArrowProjection X i T) (diagramTestExtendedCone X c i T)
    (Functor.whiskerLeft Arrow.rightFunc (diagramEtaleTestCocone X i T c).ι)
    (fun a => congrArg Quiver.Hom.op (diagramTestConeArrowTriangle X c i T a))
    (fun {j k} a => pullbackTriangleIso
      ((diagramTestExtendedCone X c i T).ι.app j).unop (X.map a).unop
      ((diagramTestExtendedCone X c i T).ι.app k).unop
      (congrArg (fun z : X.obj j ⟶ (diagramTestExtendedCone X c i T).pt => z.unop)
        ((diagramTestExtendedCone X c i T).w a)))
    (fun {j k} a => pullbackTriangleIso_mate (X.map a).unop
      ((diagramTestExtendedCone X c i T).ι.app j).unop
      ((diagramTestExtendedCone X c i T).ι.app k).unop
      (congrArg (fun z : X.obj j ⟶ (diagramTestExtendedCone X c i T).pt => z.unop)
        ((diagramTestExtendedCone X c i T).w a)))
    (fun m => diagramTestArrowSectionsMap X F i T m)
    (fun m => diagramTestArrowSectionsMap_eq_generic X F i T m)
    (diagramTestConeArrowSectionsMap X F c i T)
    (fun a => systemSquareSectionsMap_eq_sectionSystemSquareMap X F (𝟙 a.left.right)
      (diagramTestArrowSchemeMap X i T a) (diagramTestConeSchemeMap X c i T a.left)
      ((diagramEtaleTestCocone X i T c).ι.app a.right).unop
      (diagramTestConeArrowSquare X c i T a))
  row ≫ (Functor.associator Arrow.leftFunc (Under.forget i)
    (coneOriginalSectionsFunctor X F (diagramTestExtendedCone X c i T))).hom

/-- The genuine natural comparison is a composition of whole original transformations. -/
def diagramTestConeSectionsNatTrans :
    diagramTestArrowSectionsFunctor X F i T ⟶
      Arrow.leftFunc ⋙ diagramTestConeSectionsFunctor X F c i T :=
  diagramTestRawConeSectionsNatTrans X F c i T ≫
    Functor.whiskerLeft Arrow.leftFunc (diagramTestConeSectionsComparison X F c i T).hom

/-- Every row leg is the original relative pullback followed by the original chart comparison. -/
lemma diagramTestConeSectionsNatTrans_app (a : Arrow (Under i)) :
    (diagramTestConeSectionsNatTrans X F c i T).app a =
      pullbackSectionsMap (F.obj a.left.right) (diagramTestConeArrowOverHom X c i T a) ≫
        (pullbackSectionsBaseEtaleIso (c.ι.app a.left.right).unop
          (F.obj a.left.right)).hom.app (op (diagramEtaleTestLimitChart X i T c)) := by
  change (diagramTestConeArrowSectionsMap X F c i T a ≫ 𝟙 _) ≫
    (diagramTestConeSectionsIso X F c i T a.left).hom = _
  rw [Category.comp_id, diagramTestConeArrowSectionsMap_eq_pullback,
    diagramTestConeSectionsIso_hom]
  rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
