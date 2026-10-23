/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramSquareSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramPullbacks
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # The actual Arrow diagram of a compatible coefficient system -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge
variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (F : DiagramCoefficientSystem X)

/-- Sections at the target stage of the source coefficient pulled back along the indexed arrow. -/
abbrev arrowSectionsObj (a : Arrow I) : AddCommGrpCat.{u + 1} :=
  (globalSections (X.obj a.right).unop).obj
    ((inverseImage (X.map a.hom).unop).obj (F.obj a.left))

lemma arrowSectionsSquare {a b : Arrow I} (m : a ⟶ b) :
    (X.map b.hom).unop ≫ (X.map m.left).unop =
      (X.map m.right).unop ≫ (X.map a.hom).unop :=
  congrArg (fun t : X.obj a.left ⟶ X.obj b.right => t.unop)
    ((X.map_comp m.left b.hom).symm.trans
      ((congrArg X.map m.w).trans (X.map_comp a.hom m.right)))

/-- The section map of an indexing-arrow morphism, using the system transition and its square. -/
def arrowSectionsMap {a b : Arrow I} (m : a ⟶ b) :
    arrowSectionsObj X F a ⟶ arrowSectionsObj X F b :=
  squareSectionsMap (X.map a.hom).unop (X.map b.hom).unop
    (X.map m.left).unop (X.map m.right).unop (arrowSectionsSquare X m)
    (diagramInverseTransition X F m.left)

lemma arrowSectionsMap_id (a : Arrow I) :
    arrowSectionsMap X F (𝟙 a) = 𝟙 (arrowSectionsObj X F a) := by
  dsimp only [arrowSectionsMap]
  change squareSectionsMap (X.map a.hom).unop (X.map a.hom).unop
    (X.map (𝟙 a.left)).unop (X.map (𝟙 a.right)).unop _
    (diagramInverseTransition X F (𝟙 a.left)) = _
  rw [diagramInverseTransition_id]
  simp only [diagramInverseImageId, Iso.trans_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app]
  exact (squareSectionsMap_transport (X.map a.hom).unop (X.map a.hom).unop
    (𝟙 _) (X.map (𝟙 a.left)).unop (𝟙 _) (X.map (𝟙 a.right)).unop
    (congrArg (fun k : X.obj a.left ⟶ X.obj a.left => k.unop) (X.map_id a.left))
    (congrArg (fun k : X.obj a.right ⟶ X.obj a.right => k.unop) (X.map_id a.right))
    (by rw [Category.comp_id, Category.id_comp]) _
    ((inverseImageId (X.obj a.left).unop).hom.app (F.obj a.left))).trans
      (squareSectionsMap_id _ _ _)

lemma arrowSectionsMap_comp {a b c : Arrow I} (m : a ⟶ b) (n : b ⟶ c) :
    arrowSectionsMap X F (m ≫ n) = arrowSectionsMap X F m ≫ arrowSectionsMap X F n := by
  dsimp only [arrowSectionsMap]
  change squareSectionsMap (X.map a.hom).unop (X.map c.hom).unop
    (X.map (m.left ≫ n.left)).unop (X.map (m.right ≫ n.right)).unop _
    (diagramInverseTransition X F (m.left ≫ n.left)) = _
  rw [diagramInverseTransition_comp]
  simp only [diagramInverseImageComp, Iso.trans_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app]
  let e : (X.map c.hom).unop ≫ ((X.map n.left).unop ≫ (X.map m.left).unop) =
      ((X.map n.right).unop ≫ (X.map m.right).unop) ≫ (X.map a.hom).unop := by
    rw [← Category.assoc, arrowSectionsSquare X n, Category.assoc,
      arrowSectionsSquare X m, ← Category.assoc]
  let φ : (inverseImage ((X.map n.left).unop ≫ (X.map m.left).unop)).obj
      (F.obj a.left) ⟶ F.obj c.left :=
    (inverseImageComp (X.map m.left).unop (X.map n.left).unop).hom.app (F.obj a.left) ≫
      (inverseImage (X.map n.left).unop).map (diagramInverseTransition X F m.left) ≫
        diagramInverseTransition X F n.left
  have ht := squareSectionsMap_transport (X.map a.hom).unop (X.map c.hom).unop
    ((X.map n.left).unop ≫ (X.map m.left).unop) (X.map (m.left ≫ n.left)).unop
    ((X.map n.right).unop ≫ (X.map m.right).unop) (X.map (m.right ≫ n.right)).unop
    (congrArg (fun k : X.obj a.left ⟶ X.obj c.left => k.unop) (X.map_comp m.left n.left))
    (congrArg (fun k : X.obj a.right ⟶ X.obj c.right => k.unop) (X.map_comp m.right n.right))
    e (arrowSectionsSquare X (m ≫ n)) φ
  have hp := squareSectionsMap_hComp (X.map a.hom).unop (X.map b.hom).unop
    (X.map c.hom).unop (X.map m.left).unop (X.map n.left).unop
    (X.map m.right).unop (X.map n.right).unop
    (arrowSectionsSquare X m) (arrowSectionsSquare X n) e
    (diagramInverseTransition X F m.left) (diagramInverseTransition X F n.left)
  exact ht.trans hp.symm

/-- The arrow-indexed section diagram of the compatible coefficient system. -/
def arrowSectionsFunctor : Arrow I ⥤ AddCommGrpCat.{u + 1} where
  obj := arrowSectionsObj X F
  map := arrowSectionsMap X F
  map_id := arrowSectionsMap_id X F
  map_comp := arrowSectionsMap_comp X F

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
