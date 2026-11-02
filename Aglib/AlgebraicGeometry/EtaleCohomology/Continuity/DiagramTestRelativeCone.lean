/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramTestArrowSections
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramConeComparison

/-! # Original relative test-section maps into the fixed limit test scheme -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge
variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (F : DiagramCoefficientSystem X) (c : Cocone X) (i : I)
  (T : (X.obj i).unop.Etale)

/-- The original scheme cocone extended by the native limit test projection. -/
def diagramTestExtendedCone : Cocone X :=
  c.extend (diagramEtaleTestLimitChart X i T c).hom.op

/-- The literal composite map from the limit test scheme to an original stage. -/
def diagramTestConeSchemeMap (a : Under i) :
    (diagramTestExtendedCone X c i T).pt.unop ⟶ (X.obj a.right).unop :=
  ((diagramTestExtendedCone X c i T).ι.app a.right).unop

lemma diagramTestConeSquare {a b : Under i} (m : a ⟶ b) :
    diagramTestConeSchemeMap X c i T b ≫ (X.map m.right).unop =
      diagramTestConeSchemeMap X c i T a :=
  coneSquare X (diagramTestExtendedCone X c i T) m.right

lemma diagramTestConeArrowTriangle (a : Arrow (Under i)) :
    ((diagramEtaleTestCocone X i T c).ι.app a.right).unop ≫
        diagramTestArrowSchemeMap X i T a = diagramTestConeSchemeMap X c i T a.left := by
  exact congrArg Quiver.Hom.unop
    (Functor.arrowProjection_comp_cocone (Under.forget i) X (diagramEtaleTest X i T)
      (diagramEtaleTestProjection X i T) c (diagramEtaleTestCocone X i T c)
      (diagramEtaleTestLimitProjection X i T c)
      (diagramEtaleTestProjection_cocone X i T c) a)

/-- The genuine Over map giving every fixed-source row leg. -/
def diagramTestConeArrowOverHom (a : Arrow (Under i)) :
    Over.mk (diagramTestConeSchemeMap X c i T a.left) ⟶
      Over.mk (diagramTestArrowSchemeMap X i T a) :=
  Over.homMk ((diagramEtaleTestCocone X i T c).ι.app a.right).unop
    (diagramTestConeArrowTriangle X c i T a)

lemma diagramTestConeArrowSquare (a : Arrow (Under i)) :
    diagramTestConeSchemeMap X c i T a.left ≫ (X.map (𝟙 a.left.right)).unop =
      ((diagramEtaleTestCocone X i T c).ι.app a.right).unop ≫
        diagramTestArrowSchemeMap X i T a := by
  rw [X.map_id, unop_id, Category.comp_id]
  exact (diagramTestConeArrowTriangle X c i T a).symm

/-- The relative row comparison, retaining the original source coefficient. -/
def diagramTestConeArrowSectionsMap (a : Arrow (Under i)) :
    diagramTestArrowSectionsObj X F i T a ⟶
      (globalSections (diagramTestExtendedCone X c i T).pt.unop).obj
        ((inverseImage (diagramTestConeSchemeMap X c i T a.left)).obj (F.obj a.left.right)) :=
  systemSquareSectionsMap X F (𝟙 a.left.right) (diagramTestArrowSchemeMap X i T a)
    (diagramTestConeSchemeMap X c i T a.left)
    ((diagramEtaleTestCocone X i T c).ι.app a.right).unop
    (diagramTestConeArrowSquare X c i T a)

/-- The actual coefficient transition on the fixed limit test scheme. -/
def diagramTestConeSystemSectionsMap {a b : Under i} (m : a ⟶ b) :
    (globalSections (diagramTestExtendedCone X c i T).pt.unop).obj
        ((inverseImage (diagramTestConeSchemeMap X c i T a)).obj (F.obj a.right)) ⟶
      (globalSections (diagramTestExtendedCone X c i T).pt.unop).obj
        ((inverseImage (diagramTestConeSchemeMap X c i T b)).obj (F.obj b.right)) :=
  coneSystemSectionsMap X F (diagramTestExtendedCone X c i T) m.right

lemma diagramTestConeArrowSectionsMap_eq_pullback (a : Arrow (Under i)) :
    diagramTestConeArrowSectionsMap X F c i T a =
      pullbackSectionsMap (F.obj a.left.right) (diagramTestConeArrowOverHom X c i T a) := by
  dsimp only [diagramTestConeArrowSectionsMap, systemSquareSectionsMap]
  rw [diagramInverseTransition_id]
  simp only [diagramInverseImageId, Iso.trans_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app]
  have ht := squareSectionsMap_transport (diagramTestArrowSchemeMap X i T a)
    (diagramTestConeSchemeMap X c i T a.left)
    (𝟙 _) (X.map (𝟙 a.left.right)).unop
    ((diagramEtaleTestCocone X i T c).ι.app a.right).unop
    ((diagramEtaleTestCocone X i T c).ι.app a.right).unop
    (congrArg Quiver.Hom.unop (X.map_id a.left.right)) rfl
    ((Category.comp_id _).trans (diagramTestConeArrowTriangle X c i T a).symm)
    (diagramTestConeArrowSquare X c i T a)
    ((inverseImageId (X.obj a.left.right).unop).hom.app (F.obj a.left.right))
  exact ht.trans (squareSectionsMap_base_id (F.obj a.left.right)
    (diagramTestConeArrowOverHom X c i T a))

/-- Actual cone legs on the target-test indexing family, at the SAME original point. -/
private def diagramTestConeSectionLegs :
    Arrow.rightFunc ⋙ diagramEtaleTest X i T ⟶
      (Functor.const (Arrow (Under i))).obj (diagramTestExtendedCone X c i T).pt :=
  Functor.whiskerLeft Arrow.rightFunc (diagramEtaleTestCocone X i T c).ι

private theorem diagramTestConeSectionTriangle (a : Arrow (Under i)) :
    (diagramTestArrowProjection X i T).app a ≫
        (diagramTestConeSectionLegs X c i T).app a =
      (diagramTestExtendedCone X c i T).ι.app a.left.right :=
  congrArg Quiver.Hom.op (diagramTestConeArrowTriangle X c i T a)

/-- The original relative row map is the shared indexed cone map. -/
private lemma diagramTestConeArrowSectionsMap_eq_generic (a : Arrow (Under i)) :
    diagramTestConeArrowSectionsMap X F c i T a =
      schemeSectionData.indexedConeMap X F (Arrow.leftFunc ⋙ Under.forget i)
        (Arrow.rightFunc ⋙ diagramEtaleTest X i T) (diagramTestArrowProjection X i T)
        (diagramTestExtendedCone X c i T) (diagramTestConeSectionLegs X c i T)
        (diagramTestConeSectionTriangle X c i T) a :=
  systemSquareSectionsMap_eq_sectionSystemSquareMap X F (𝟙 a.left.right)
    (diagramTestArrowSchemeMap X i T a) (diagramTestConeSchemeMap X c i T a.left)
    ((diagramEtaleTestCocone X i T c).ι.app a.right).unop
    (diagramTestConeArrowSquare X c i T a)

/-- The original fixed-apex transition is the same generic cone-system map. -/
lemma diagramTestConeSystemSectionsMap_eq_generic {a b : Under i} (m : a ⟶ b) :
    diagramTestConeSystemSectionsMap X F c i T m =
      schemeSectionData.coneSystemMap X F (diagramTestExtendedCone X c i T) m.right :=
  coneSystemSectionsMap_eq_sectionConeSystemMap X F (diagramTestExtendedCone X c i T) m.right

lemma diagramTestConeArrowSectionsMap_naturality {a b : Arrow (Under i)} (m : a ⟶ b) :
    diagramTestArrowSectionsMap X F i T m ≫ diagramTestConeArrowSectionsMap X F c i T b =
      diagramTestConeArrowSectionsMap X F c i T a ≫
        diagramTestConeSystemSectionsMap X F c i T m.left := by
  let Va : AddCommGrpCat.{u + 1} :=
    (globalSections (diagramTestExtendedCone X c i T).pt.unop).obj
      ((inverseImage (diagramTestConeSchemeMap X c i T a.left)).obj (F.obj a.left.right))
  let Vb : AddCommGrpCat.{u + 1} :=
    (globalSections (diagramTestExtendedCone X c i T).pt.unop).obj
      ((inverseImage (diagramTestConeSchemeMap X c i T b.left)).obj (F.obj b.left.right))
  have h := schemeSectionData.indexedConeMap_naturality schemeAdjunctionData_coherent X F
    (Arrow.leftFunc ⋙ Under.forget i) (Arrow.rightFunc ⋙ diagramEtaleTest X i T)
    (diagramTestArrowProjection X i T) (diagramTestExtendedCone X c i T)
    (diagramTestConeSectionLegs X c i T) (diagramTestConeSectionTriangle X c i T) m
  have hl := congrArg₂
    (fun (f : diagramTestArrowSectionsObj X F i T a ⟶ diagramTestArrowSectionsObj X F i T b)
      (g : diagramTestArrowSectionsObj X F i T b ⟶ Vb) => f ≫ g)
    (diagramTestArrowSectionsMap_eq_generic X F i T m)
    (diagramTestConeArrowSectionsMap_eq_generic X F c i T b)
  have hr := congrArg₂
    (fun (f : diagramTestArrowSectionsObj X F i T a ⟶ Va) (g : Va ⟶ Vb) => f ≫ g)
    (diagramTestConeArrowSectionsMap_eq_generic X F c i T a)
    (diagramTestConeSystemSectionsMap_eq_generic X F c i T m.left)
  have hfinal := hl.trans (h.trans hr.symm)
  exact hfinal

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
