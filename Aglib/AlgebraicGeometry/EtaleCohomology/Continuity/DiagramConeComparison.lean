/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramConeSquares
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramSquareTopIdentity

/-! # The original Arrow-to-cone section comparison -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge
variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (F : DiagramCoefficientSystem X) (c : Cocone X)

lemma coneSystemSectionsMap_eq {i j : I} (a : i ⟶ j) :
    coneSystemSectionsMap X F c a =
      (globalSections c.pt.unop).map (coneCoefficientMap X c F a) :=
  squareSectionsMap_top_id (c.ι.app i).unop (c.ι.app j).unop (X.map a).unop
    (coneSquare X c a) (diagramInverseTransition X F a)

/-- The relative cone leg without any chosen comparison isomorphism. -/
def coneArrowOverHom (a : Arrow I) :
    Over.mk (c.ι.app a.left).unop ⟶ Over.mk (X.map a.hom).unop :=
  Over.homMk (c.ι.app a.right).unop (coneSquare X c a.hom)

lemma coneArrowSectionsMap_eq_pullback (a : Arrow I) :
    coneArrowSectionsMap X F c a = pullbackSectionsMap (F.obj a.left) (coneArrowOverHom X c a) := by
  dsimp only [coneArrowSectionsMap, systemSquareSectionsMap]
  rw [diagramInverseTransition_id]
  simp only [diagramInverseImageId, Iso.trans_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app]
  have ht := squareSectionsMap_transport (X.map a.hom).unop (c.ι.app a.left).unop
    (𝟙 _) (X.map (𝟙 a.left)).unop (c.ι.app a.right).unop (c.ι.app a.right).unop
    (congrArg (fun k : X.obj a.left ⟶ X.obj a.left => k.unop) (X.map_id a.left)) rfl
    ((Category.comp_id (c.ι.app a.left).unop).trans (coneSquare X c a.hom).symm)
    (coneArrowSquare X c a) ((inverseImageId (X.obj a.left).unop).hom.app (F.obj a.left))
  exact ht.trans (squareSectionsMap_base_id (F.obj a.left) (coneArrowOverHom X c a))

section Small
variable {J : Type (u + 1)} [SmallCategory J]
  (Y : J ⥤ Scheme.{u}ᵒᵖ) (G : DiagramCoefficientSystem Y) (d : Cocone Y)

/-- The actual natural comparison used by the double-colimit argument. -/
def arrowToConeSections : arrowSectionsFunctor Y G ⟶
    Arrow.leftFunc ⋙ coneCoefficientSectionsFunctor Y d G where
  app a := coneArrowSectionsMap Y G d a
  naturality a _ m :=
    (coneArrowSectionsMap_naturality Y G d m).trans
      (congrArg (fun k => coneArrowSectionsMap Y G d a ≫ k)
        (coneSystemSectionsMap_eq Y G d m.left))

end Small
end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
