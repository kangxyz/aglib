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
  simp only [systemSquareSectionsMap_eq_sectionSystemSquareMap]
  exact schemeSectionData.systemSquareMap_congr X F a b hab f.op g.op h.op
    (congrArg Quiver.Hom.op ea) (congrArg Quiver.Hom.op eb)

variable (c : Cocone X)

lemma coneSquare {i j : I} (a : i ⟶ j) :
    (c.ι.app j).unop ≫ (X.map a).unop = (c.ι.app i).unop :=
  congrArg Quiver.Hom.unop (InjectiveSystem.AdjunctionData.Sections.coneSquare X c a)

lemma coneArrowSquare (a : Arrow I) :
    (c.ι.app a.left).unop ≫ (X.map (𝟙 a.left)).unop =
      (c.ι.app a.right).unop ≫ (X.map a.hom).unop :=
  congrArg Quiver.Hom.unop (InjectiveSystem.AdjunctionData.Sections.coneArrowSquare X c a)

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

/-- The actual native cone leg is the generic original-square cone leg. -/
lemma coneArrowSectionsMap_eq_sectionConeArrowMap (a : Arrow I) :
    coneArrowSectionsMap X F c a = schemeSectionData.coneArrowMap X F c a := by
  exact systemSquareSectionsMap_eq_sectionSystemSquareMap X F (𝟙 a.left)
    (X.map a.hom).unop (c.ι.app a.left).unop (c.ι.app a.right).unop
    (coneArrowSquare X c a)

/-- The actual native apex transition is the generic original-square transition. -/
lemma coneSystemSectionsMap_eq_sectionConeSystemMap {i j : I} (a : i ⟶ j) :
    coneSystemSectionsMap X F c a = schemeSectionData.coneSystemMap X F c a := by
  exact systemSquareSectionsMap_eq_sectionSystemSquareMap X F a
    (c.ι.app i).unop (c.ι.app j).unop (𝟙 _)
    ((coneSquare X c a).trans (Category.id_comp _).symm)

lemma coneArrowSectionsMap_naturality {a b : Arrow I} (m : a ⟶ b) :
    arrowSectionsMap X F m ≫ coneArrowSectionsMap X F c b =
      coneArrowSectionsMap X F c a ≫ coneSystemSectionsMap X F c m.left := by
  simp only [arrowSectionsMap_eq_sectionArrowMap,
    coneArrowSectionsMap_eq_sectionConeArrowMap, coneSystemSectionsMap_eq_sectionConeSystemMap]
  exact schemeSectionData.coneArrowMap_naturality schemeAdjunctionData_coherent X F c m

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
