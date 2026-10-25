/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramTestRelativeCone
public import Mathlib.CategoryTheory.Filtered.Final
public import Mathlib.CategoryTheory.Limits.Opposites

/-! # Fixed-coefficient relative scheme rows of the original test-object diagram -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
universe u uI vI
attribute [local instance] hasSheafifyLarge
variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (c : Cocone X) (i : I) (T : (X.obj i).unop.Etale) (a : Under i)

lemma diagramTestRelativeTail_w {b d : Under a} (m : b ⟶ d) :
    ((diagramEtaleTest X i T).map m.right).unop ≫
        diagramTestArrowSchemeMap X i T (Arrow.mk b.hom) =
      diagramTestArrowSchemeMap X i T (Arrow.mk d.hom) := by
  have h := diagramTestArrowSquare X i T ((SchemeSystemColimits.tailToArrow a).map m)
  change diagramTestArrowSchemeMap X i T (Arrow.mk d.hom) ≫
      (X.map (𝟙 a.right)).unop = _ at h
  rw [X.map_id, unop_id] at h
  exact h.symm.trans (Category.comp_id _)

/-- A row of test schemes over the actual fixed source coefficient scheme. -/
def diagramTestRelativeTail : Under a ⥤ (Over (X.obj a.right).unop)ᵒᵖ where
  obj b := op (Over.mk (diagramTestArrowSchemeMap X i T (Arrow.mk b.hom)))
  map {b d} m := (Over.homMk
    (U := Over.mk (diagramTestArrowSchemeMap X i T (Arrow.mk d.hom)))
    (V := Over.mk (diagramTestArrowSchemeMap X i T (Arrow.mk b.hom)))
    ((diagramEtaleTest X i T).map m.right).unop
    (diagramTestRelativeTail_w X i T a m)).op
  map_id b := by
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    exact congrArg Quiver.Hom.unop ((diagramEtaleTest X i T).map_id b.right)
  map_comp m n := by
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    exact congrArg Quiver.Hom.unop ((diagramEtaleTest X i T).map_comp m.right n.right)

/-- The row cone is the original test-limit structural cocone over the fixed source. -/
def diagramTestRelativeTailCocone : Cocone (diagramTestRelativeTail X i T a) where
  pt := op (Over.mk (diagramTestConeSchemeMap X c i T a))
  ι.app b := (diagramTestConeArrowOverHom X c i T (Arrow.mk b.hom)).op
  ι.naturality b d m := by
    apply Quiver.Hom.unop_inj
    apply Over.OverMorphism.ext
    exact coneSquare (diagramEtaleTest X i T) (diagramEtaleTestCocone X i T c) m.right

/-- Native inverse-cone form of the same actual fixed-coefficient row. -/
def diagramTestRelativeTailCone : Cone (diagramTestRelativeTail X i T a).leftOp :=
  coneLeftOpOfCocone (diagramTestRelativeTailCocone X c i T a)

/-- A genuine test-scheme limit remains a limit on the actual fixed-source row. -/
def isLimitDiagramTestRelativeTail [IsFiltered (Under i)]
    (h : IsColimit (diagramEtaleTestCocone X i T c)) :
    IsLimit ((Over.forget (X.obj a.right).unop).mapCone
      (diagramTestRelativeTailCone X c i T a)) :=
  isLimitConeLeftOpOfCocone _
    ((Functor.Final.isColimitWhiskerEquiv (Under.forget a)
      (diagramEtaleTestCocone X i T c)).symm h)

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
