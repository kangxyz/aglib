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
  have hp := congrArg Quiver.Hom.unop (diagramEtaleTestProjection_cocone X i T c a.right)
  change ((diagramEtaleTestCocone X i T c).ι.app a.right).unop ≫
      (diagramEtaleTestChart X i T a.right).hom =
    (diagramEtaleTestLimitChart X i T c).hom ≫ (c.ι.app a.right.right).unop at hp
  change _ ≫ ((diagramEtaleTestChart X i T a.right).hom ≫
      (X.map a.hom.right).unop) = _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ (X.map a.hom.right).unop) hp).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun k => (diagramEtaleTestLimitChart X i T c).hom ≫ k)
          (coneSquare X c a.hom.right))))

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

lemma diagramTestConeArrowSectionsMap_naturality {a b : Arrow (Under i)} (m : a ⟶ b) :
    diagramTestArrowSectionsMap X F i T m ≫ diagramTestConeArrowSectionsMap X F c i T b =
      diagramTestConeArrowSectionsMap X F c i T a ≫
        diagramTestConeSystemSectionsMap X F c i T m.left := by
  let e : diagramTestConeSchemeMap X c i T b.left ≫ (X.map m.left.right).unop =
      ((diagramEtaleTestCocone X i T c).ι.app a.right).unop ≫
        diagramTestArrowSchemeMap X i T a :=
    (diagramTestConeSquare X c i T m.left).trans
      (diagramTestConeArrowTriangle X c i T a).symm
  let e₁ : diagramTestConeSchemeMap X c i T b.left ≫
      (X.map (m.left.right ≫ 𝟙 b.left.right)).unop =
      ((diagramEtaleTestCocone X i T c).ι.app a.right).unop ≫
        diagramTestArrowSchemeMap X i T a := by simpa only [Category.comp_id] using e
  let e₂ : diagramTestConeSchemeMap X c i T b.left ≫
      (X.map (𝟙 a.left.right ≫ m.left.right)).unop =
      ((diagramEtaleTestCocone X i T c).ι.app a.right).unop ≫
        diagramTestArrowSchemeMap X i T a := by simpa only [Category.id_comp] using e
  have h₁ := systemSquareSectionsMap_comp X F m.left.right (𝟙 b.left.right)
    (diagramTestArrowSchemeMap X i T a) (diagramTestArrowSchemeMap X i T b)
    (diagramTestConeSchemeMap X c i T b.left)
    ((diagramEtaleTest X i T).map m.right).unop
    ((diagramEtaleTestCocone X i T c).ι.app b.right).unop
    ((diagramEtaleTestCocone X i T c).ι.app a.right).unop
    (coneSquare (diagramEtaleTest X i T) (diagramEtaleTestCocone X i T c) m.right).symm
    (diagramTestArrowSquare X i T m) (diagramTestConeArrowSquare X c i T b) e₁
  have h₂ := systemSquareSectionsMap_comp X F (𝟙 a.left.right) m.left.right
    (diagramTestArrowSchemeMap X i T a) (diagramTestConeSchemeMap X c i T a.left)
    (diagramTestConeSchemeMap X c i T b.left)
    ((diagramEtaleTestCocone X i T c).ι.app a.right).unop (𝟙 _)
    ((diagramEtaleTestCocone X i T c).ι.app a.right).unop
    (Category.id_comp _).symm (diagramTestConeArrowSquare X c i T a)
    ((diagramTestConeSquare X c i T m.left).trans (Category.id_comp _).symm) e₂
  have hi := systemSquareSectionsMap_congr X F (m.left.right ≫ 𝟙 b.left.right) m.left.right
    (Category.comp_id _) (diagramTestArrowSchemeMap X i T a)
    (diagramTestConeSchemeMap X c i T b.left)
    ((diagramEtaleTestCocone X i T c).ι.app a.right).unop e₁ e
  have hj := systemSquareSectionsMap_congr X F (𝟙 a.left.right ≫ m.left.right) m.left.right
    (Category.id_comp _) (diagramTestArrowSchemeMap X i T a)
    (diagramTestConeSchemeMap X c i T b.left)
    ((diagramEtaleTestCocone X i T c).ι.app a.right).unop e₂ e
  exact h₁.symm.trans (hi.trans (hj.symm.trans h₂))

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
