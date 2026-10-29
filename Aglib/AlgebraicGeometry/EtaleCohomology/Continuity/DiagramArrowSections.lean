/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramSquareSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramPullbacks
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.SectionArrows

/-! # The actual Arrow diagram of a compatible coefficient system -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge

/-- The actual global-section functors and original adjunction-unit pullbacks. -/
def schemeSectionData :
    schemeAdjunctionData.Sections AddCommGrpCat.{u + 1} where
  value S := globalSections S.unop
  pullback a := globalSectionsPullbackNatTrans a.unop
  id S F := by
    change globalSectionsPullback (𝟙 S.unop) F ≫
      (globalSections S.unop).map ((schemeAdjunctionData.leftIdIso S).hom.app F) = 𝟙 _
    rw [schemeLeftIdIso_eq_inverseImageId]
    exact globalSectionsPullback_id S.unop F
  comp {i j k} a b F := by
    change globalSectionsPullback (b.unop ≫ a.unop) F ≫
        (globalSections k.unop).map ((schemeAdjunctionData.leftCompIso a b).hom.app F) =
      globalSectionsPullback a.unop F ≫
        globalSectionsPullback b.unop ((inverseImage a.unop).obj F)
    rw [schemeLeftCompIso_eq_inverseImageComp]
    exact globalSectionsPullback_comp a.unop b.unop F

/-- The generic section square is the whole original étale section map. -/
lemma schemeSectionSquareMap_eq {S₀ X₀ S₁ X₁ : Scheme.{u}ᵒᵖ}
    (f₀ : S₀ ⟶ X₀) (f₁ : S₁ ⟶ X₁) (g : S₀ ⟶ S₁) (h : X₀ ⟶ X₁)
    (e : g ≫ f₁ = f₀ ≫ h)
    {F : AbelianSheaf.{u, u + 1} S₀.unop} {G : AbelianSheaf.{u, u + 1} S₁.unop}
    (φ : (inverseImage g.unop).obj F ⟶ G) :
    schemeSectionData.squareMap f₀ f₁ g h e φ =
      squareSectionsMap f₀.unop f₁.unop g.unop h.unop (congrArg Quiver.Hom.unop e) φ := by
  change globalSectionsPullback h.unop ((inverseImage f₀.unop).obj F) ≫
      (globalSections X₁.unop).map
        (schemeAdjunctionData.squareCoefficientMap f₀ f₁ g h e φ) = _
  rw [schemeSquareCoefficientMap_eq_squareCoefficientMap]
  rfl

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (F : DiagramCoefficientSystem X)

/-- Sections at the target stage of the source coefficient pulled back along the indexed arrow. -/
abbrev arrowSectionsObj (a : Arrow I) : AddCommGrpCat.{u + 1} :=
  (globalSections (X.obj a.right).unop).obj
    ((inverseImage (X.map a.hom).unop).obj (F.obj a.left))

lemma arrowSectionsSquare {a b : Arrow I} (m : a ⟶ b) :
    (X.map b.hom).unop ≫ (X.map m.left).unop =
      (X.map m.right).unop ≫ (X.map a.hom).unop :=
  congrArg Quiver.Hom.unop
    (InjectiveSystem.AdjunctionData.Sections.arrowSquare X m)

/-- The section map of an indexing-arrow morphism, using the system transition and its square. -/
def arrowSectionsMap {a b : Arrow I} (m : a ⟶ b) :
    arrowSectionsObj X F a ⟶ arrowSectionsObj X F b :=
  squareSectionsMap (X.map a.hom).unop (X.map b.hom).unop
    (X.map m.left).unop (X.map m.right).unop (arrowSectionsSquare X m)
    (diagramInverseTransition X F m.left)

/-- The native map is the same complete square map used by the generic Arrow construction. -/
lemma arrowSectionsMap_eq_sectionArrowMap {a b : Arrow I} (m : a ⟶ b) :
    arrowSectionsMap X F m = schemeSectionData.arrowMap X F m := by
  symm
  exact schemeSectionSquareMap_eq (X.map a.hom) (X.map b.hom)
    (X.map m.left) (X.map m.right)
    (InjectiveSystem.AdjunctionData.Sections.arrowSquare X m)
    (diagramInverseTransition X F m.left)

lemma arrowSectionsMap_id (a : Arrow I) :
    arrowSectionsMap X F (𝟙 a) = 𝟙 (arrowSectionsObj X F a) := by
  rw [arrowSectionsMap_eq_sectionArrowMap]
  exact schemeSectionData.arrowMap_id schemeAdjunctionData_coherent X F a

lemma arrowSectionsMap_comp {a b c : Arrow I} (m : a ⟶ b) (n : b ⟶ c) :
    arrowSectionsMap X F (m ≫ n) = arrowSectionsMap X F m ≫ arrowSectionsMap X F n := by
  simp only [arrowSectionsMap_eq_sectionArrowMap]
  exact schemeSectionData.arrowMap_comp schemeAdjunctionData_coherent X F m n

/-- The arrow-indexed section diagram, retaining the original native object and map values. -/
def arrowSectionsFunctor : Arrow I ⥤ AddCommGrpCat.{u + 1} :=
  schemeSectionData.arrowFunctorWithMap schemeAdjunctionData_coherent X F
    (arrowSectionsMap X F) (arrowSectionsMap_eq_sectionArrowMap X F)

/-- The shared construction stores the original native Arrow morphism. -/
lemma arrowSectionsFunctor_map {a b : Arrow I} (m : a ⟶ b) :
    (arrowSectionsFunctor X F).map m = arrowSectionsMap X F m := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
