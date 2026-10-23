/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramEtaleTest
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramSystemSquares

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

/-- The target test scheme maps to the original source coefficient scheme. -/
def diagramTestArrowSchemeMap (a : Arrow (Under i)) :
    ((diagramEtaleTest X i T).obj a.right).unop ⟶ (X.obj a.left.right).unop :=
  (diagramEtaleTestChart X i T a.right).hom ≫ (X.map a.hom.right).unop

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
  have hs := arrowSectionsSquare (diagramSchemeTail X i) m
  change (X.map b.hom.right).unop ≫ (X.map m.left.right).unop =
    (X.map m.right.right).unop ≫ (X.map a.hom.right).unop at hs
  have hp := diagramEtaleTest_map_fst X i T m.right
  change ((diagramEtaleTest X i T).map m.right).unop ≫
      (diagramEtaleTestChart X i T a.right).hom =
    (diagramEtaleTestChart X i T b.right).hom ≫ (X.map m.right.right).unop at hp
  dsimp only [diagramTestArrowSchemeMap]
  change ((diagramEtaleTestChart X i T b.right).hom ≫ (X.map b.hom.right).unop) ≫
      (X.map m.left.right).unop =
    ((diagramEtaleTest X i T).map m.right).unop ≫
      ((diagramEtaleTestChart X i T a.right).hom ≫ (X.map a.hom.right).unop)
  rw [Category.assoc, hs, ← Category.assoc, ← hp]
  exact Category.assoc _ _ _

/-- Original square transfer for a morphism of test arrows. -/
def diagramTestArrowSectionsMap {a b : Arrow (Under i)} (m : a ⟶ b) :
    diagramTestArrowSectionsObj X F i T a ⟶ diagramTestArrowSectionsObj X F i T b :=
  systemSquareSectionsMap X F m.left.right (diagramTestArrowSchemeMap X i T a)
    (diagramTestArrowSchemeMap X i T b) ((diagramEtaleTest X i T).map m.right).unop
    (diagramTestArrowSquare X i T m)

lemma diagramTestArrowSectionsMap_id (a : Arrow (Under i)) :
    diagramTestArrowSectionsMap X F i T (𝟙 a) = 𝟙 (diagramTestArrowSectionsObj X F i T a) := by
  dsimp only [diagramTestArrowSectionsMap, systemSquareSectionsMap]
  change squareSectionsMap (diagramTestArrowSchemeMap X i T a)
    (diagramTestArrowSchemeMap X i T a) (X.map (𝟙 a.left.right)).unop
    ((diagramEtaleTest X i T).map (𝟙 a.right)).unop _
    (diagramInverseTransition X F (𝟙 a.left.right)) = _
  rw [diagramInverseTransition_id]
  simp only [diagramInverseImageId, Iso.trans_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app]
  exact (squareSectionsMap_transport (diagramTestArrowSchemeMap X i T a)
    (diagramTestArrowSchemeMap X i T a)
    (𝟙 _) (X.map (𝟙 a.left.right)).unop
    (𝟙 _) ((diagramEtaleTest X i T).map (𝟙 a.right)).unop
    (congrArg Quiver.Hom.unop (X.map_id a.left.right))
    (congrArg Quiver.Hom.unop ((diagramEtaleTest X i T).map_id a.right))
    ((Category.comp_id _).trans (Category.id_comp _).symm) _
    ((inverseImageId (X.obj a.left.right).unop).hom.app (F.obj a.left.right))).trans
      (squareSectionsMap_id _ _ _)

lemma diagramTestArrowSectionsMap_comp {a b c : Arrow (Under i)} (m : a ⟶ b) (n : b ⟶ c) :
    diagramTestArrowSectionsMap X F i T (m ≫ n) =
      diagramTestArrowSectionsMap X F i T m ≫ diagramTestArrowSectionsMap X F i T n :=
  systemSquareSectionsMap_comp X F m.left.right n.left.right
    (diagramTestArrowSchemeMap X i T a) (diagramTestArrowSchemeMap X i T b)
    (diagramTestArrowSchemeMap X i T c)
    ((diagramEtaleTest X i T).map m.right).unop
    ((diagramEtaleTest X i T).map n.right).unop
    ((diagramEtaleTest X i T).map (m.right ≫ n.right)).unop
    (congrArg Quiver.Hom.unop ((diagramEtaleTest X i T).map_comp m.right n.right))
    (diagramTestArrowSquare X i T m) (diagramTestArrowSquare X i T n)
    (diagramTestArrowSquare X i T (m ≫ n))

/-- The actual Ab-valued double-tail functor. -/
def diagramTestArrowSectionsFunctor : Arrow (Under i) ⥤ AddCommGrpCat.{u + 1} where
  obj := diagramTestArrowSectionsObj X F i T
  map := diagramTestArrowSectionsMap X F i T
  map_id := diagramTestArrowSectionsMap_id X F i T
  map_comp := diagramTestArrowSectionsMap_comp X F i T

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
