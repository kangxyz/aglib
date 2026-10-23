/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramSystemSquares
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramLimitSections

/-! # Original cone squares for the compatible-system double colimit -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge
variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (F : DiagramCoefficientSystem X)

lemma systemSquareSectionsMap_congr {i j : I} (a b : i ⟶ j) (hab : a = b)
    {Y Z : Scheme.{u}} (f : Y ⟶ (X.obj i).unop) (g : Z ⟶ (X.obj j).unop) (h : Z ⟶ Y)
    (ea : g ≫ (X.map a).unop = h ≫ f) (eb : g ≫ (X.map b).unop = h ≫ f) :
    systemSquareSectionsMap X F a f g h ea = systemSquareSectionsMap X F b f g h eb := by
  subst b
  rfl

variable (c : Cocone X)

lemma coneSquare {i j : I} (a : i ⟶ j) :
    (c.ι.app j).unop ≫ (X.map a).unop = (c.ι.app i).unop :=
  congrArg (fun k : X.obj i ⟶ c.pt => k.unop) (c.w a)

lemma coneArrowSquare (a : Arrow I) :
    (c.ι.app a.left).unop ≫ (X.map (𝟙 a.left)).unop =
      (c.ι.app a.right).unop ≫ (X.map a.hom).unop := by
  rw [X.map_id, CategoryTheory.unop_id, Category.comp_id]
  exact (coneSquare X c a.hom).symm

/-- Pull arrow-indexed sections to the cone point with their source-stage coefficient. -/
def coneArrowSectionsMap (a : Arrow I) :
    arrowSectionsObj X F a ⟶ (globalSections c.pt.unop).obj (coneCoefficientObj X c F a.left) :=
  systemSquareSectionsMap X F (𝟙 a.left) (X.map a.hom).unop
    (c.ι.app a.left).unop (c.ι.app a.right).unop (coneArrowSquare X c a)

/-- The section map at the cone point induced by a coefficient-system transition. -/
def coneSystemSectionsMap {i j : I} (a : i ⟶ j) :
    (globalSections c.pt.unop).obj (coneCoefficientObj X c F i) ⟶
      (globalSections c.pt.unop).obj (coneCoefficientObj X c F j) :=
  systemSquareSectionsMap X F a (c.ι.app i).unop (c.ι.app j).unop (𝟙 _)
    ((coneSquare X c a).trans (Category.id_comp _).symm)

lemma coneArrowSectionsMap_naturality {a b : Arrow I} (m : a ⟶ b) :
    arrowSectionsMap X F m ≫ coneArrowSectionsMap X F c b =
      coneArrowSectionsMap X F c a ≫ coneSystemSectionsMap X F c m.left := by
  let e : (c.ι.app b.left).unop ≫ (X.map m.left).unop =
      (c.ι.app a.right).unop ≫ (X.map a.hom).unop :=
    (coneSquare X c m.left).trans (coneSquare X c a.hom).symm
  let e₁ : (c.ι.app b.left).unop ≫ (X.map (m.left ≫ 𝟙 b.left)).unop =
      (c.ι.app a.right).unop ≫ (X.map a.hom).unop := by
    simpa only [Category.comp_id] using e
  let e₂ : (c.ι.app b.left).unop ≫ (X.map (𝟙 a.left ≫ m.left)).unop =
      (c.ι.app a.right).unop ≫ (X.map a.hom).unop := by
    simpa only [Category.id_comp] using e
  have h₁ := systemSquareSectionsMap_comp X F m.left (𝟙 b.left)
    (X.map a.hom).unop (X.map b.hom).unop (c.ι.app b.left).unop
    (X.map m.right).unop (c.ι.app b.right).unop (c.ι.app a.right).unop
    (coneSquare X c m.right).symm (arrowSectionsSquare X m) (coneArrowSquare X c b) e₁
  have h₂ := systemSquareSectionsMap_comp X F (𝟙 a.left) m.left
    (X.map a.hom).unop (c.ι.app a.left).unop (c.ι.app b.left).unop
    (c.ι.app a.right).unop (𝟙 _) (c.ι.app a.right).unop
    (Category.id_comp _).symm (coneArrowSquare X c a)
    ((coneSquare X c m.left).trans (Category.id_comp _).symm) e₂
  have hi := systemSquareSectionsMap_congr X F (m.left ≫ 𝟙 b.left) m.left
    (Category.comp_id m.left) (X.map a.hom).unop (c.ι.app b.left).unop
    (c.ι.app a.right).unop e₁ e
  have hj := systemSquareSectionsMap_congr X F (𝟙 a.left ≫ m.left) m.left
    (Category.id_comp m.left) (X.map a.hom).unop (c.ι.app b.left).unop
    (c.ι.app a.right).unop e₂ e
  exact h₁.symm.trans (hi.trans (hj.symm.trans h₂))

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
