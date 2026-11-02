/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramEtaleTest
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramSystemSquares
public import Aglib.CategoryTheory.Filtered.SectionDiagrams

/-! # Original coefficient sections on the double tail of an étale test object

The coefficient at an arrow's source is pulled along the literal composite map
from the target test scheme. No pulled coefficient-colimit comparison is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge
variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (F : DiagramCoefficientSystem X) (i : I) (T : (X.obj i).unop.Etale)

/-- The actual source-coefficient/target-test structural family on the double tail. -/
def diagramTestArrowProjection :
    (Arrow.leftFunc ⋙ Under.forget i) ⋙ X ⟶ Arrow.rightFunc ⋙ diagramEtaleTest X i T :=
  Functor.arrowProjection (Under.forget i) X (diagramEtaleTest X i T)
    (diagramEtaleTestProjection X i T)

/-- The target test scheme maps to the original source coefficient scheme. -/
def diagramTestArrowSchemeMap (a : Arrow (Under i)) :
    ((diagramEtaleTest X i T).obj a.right).unop ⟶ (X.obj a.left.right).unop :=
  ((diagramTestArrowProjection X i T).app a).unop

/-- The shared structural construction keeps the literal original composite. -/
theorem diagramTestArrowSchemeMap_value (a : Arrow (Under i)) :
    diagramTestArrowSchemeMap X i T a =
      (diagramEtaleTestChart X i T a.right).hom ≫ (X.map a.hom.right).unop := rfl

lemma diagramTestArrowSchemeMap_diagonal (a : Under i) :
    diagramTestArrowSchemeMap X i T (Arrow.mk (𝟙 a)) =
      (diagramEtaleTestChart X i T a).hom := by
  change (diagramEtaleTestChart X i T a).hom ≫ (X.map (𝟙 a.right)).unop = _
  rw [X.map_id, unop_id]
  exact Category.comp_id _

/-- Literal relative sections of the original source coefficient. -/
abbrev diagramTestArrowSectionsObj (a : Arrow (Under i)) : AddCommGrpCat.{u + 1} :=
  (globalSections ((diagramEtaleTest X i T).obj a.right).unop).obj
    ((inverseImage (diagramTestArrowSchemeMap X i T a)).obj (F.obj a.left.right))

lemma diagramTestArrowSquare {a b : Arrow (Under i)} (m : a ⟶ b) :
    diagramTestArrowSchemeMap X i T b ≫ (X.map m.left.right).unop =
      ((diagramEtaleTest X i T).map m.right).unop ≫ diagramTestArrowSchemeMap X i T a := by
  exact congrArg Quiver.Hom.unop ((diagramTestArrowProjection X i T).naturality m)

/-- Original square transfer for a morphism of test arrows. -/
def diagramTestArrowSectionsMap {a b : Arrow (Under i)} (m : a ⟶ b) :
    diagramTestArrowSectionsObj X F i T a ⟶ diagramTestArrowSectionsObj X F i T b :=
  systemSquareSectionsMap X F m.left.right (diagramTestArrowSchemeMap X i T a)
    (diagramTestArrowSchemeMap X i T b) ((diagramEtaleTest X i T).map m.right).unop
    (diagramTestArrowSquare X i T m)

/-- The original native square map is the shared actual indexed square. -/
lemma diagramTestArrowSectionsMap_eq_generic {a b : Arrow (Under i)} (m : a ⟶ b) :
    diagramTestArrowSectionsMap X F i T m =
      schemeSectionData.indexedMap X F (Arrow.leftFunc ⋙ Under.forget i)
        (Arrow.rightFunc ⋙ diagramEtaleTest X i T) (diagramTestArrowProjection X i T) m :=
  systemSquareSectionsMap_eq_sectionSystemSquareMap X F m.left.right
    (diagramTestArrowSchemeMap X i T a) (diagramTestArrowSchemeMap X i T b)
    ((diagramEtaleTest X i T).map m.right).unop (diagramTestArrowSquare X i T m)

lemma diagramTestArrowSectionsMap_id (a : Arrow (Under i)) :
    diagramTestArrowSectionsMap X F i T (𝟙 a) = 𝟙 (diagramTestArrowSectionsObj X F i T a) := by
  exact (diagramTestArrowSectionsMap_eq_generic X F i T (𝟙 a)).trans
    (schemeSectionData.indexedMap_id schemeAdjunctionData_coherent X F
      (Arrow.leftFunc ⋙ Under.forget i) (Arrow.rightFunc ⋙ diagramEtaleTest X i T)
      (diagramTestArrowProjection X i T) a)

lemma diagramTestArrowSectionsMap_comp {a b c : Arrow (Under i)} (m : a ⟶ b) (n : b ⟶ c) :
    diagramTestArrowSectionsMap X F i T (m ≫ n) =
      diagramTestArrowSectionsMap X F i T m ≫ diagramTestArrowSectionsMap X F i T n := by
  have hcomp := schemeSectionData.indexedMap_comp schemeAdjunctionData_coherent X F
    (Arrow.leftFunc ⋙ Under.forget i) (Arrow.rightFunc ⋙ diagramEtaleTest X i T)
    (diagramTestArrowProjection X i T) m n
  have hmaps := congrArg₂
    (fun (f : diagramTestArrowSectionsObj X F i T a ⟶ diagramTestArrowSectionsObj X F i T b)
      (g : diagramTestArrowSectionsObj X F i T b ⟶ diagramTestArrowSectionsObj X F i T c) => f ≫ g)
    (diagramTestArrowSectionsMap_eq_generic X F i T m)
    (diagramTestArrowSectionsMap_eq_generic X F i T n)
  have hfinal := (diagramTestArrowSectionsMap_eq_generic X F i T (m ≫ n)).trans
    (hcomp.trans hmaps.symm)
  exact hfinal

/-- The actual Ab-valued double-tail functor. -/
def diagramTestArrowSectionsFunctor : Arrow (Under i) ⥤ AddCommGrpCat.{u + 1} :=
  schemeSectionData.indexedFunctorWithMap schemeAdjunctionData_coherent X F
    (Arrow.leftFunc ⋙ Under.forget i) (Arrow.rightFunc ⋙ diagramEtaleTest X i T)
    (diagramTestArrowProjection X i T)
    (fun m => diagramTestArrowSectionsMap X F i T m)
    (fun m => diagramTestArrowSectionsMap_eq_generic X F i T m)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
