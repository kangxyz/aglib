/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.ConeRightTail
public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramDirectImageTriangleComp

/-! # The original fixed-stage right-image coefficient cocone

All coefficients in the tail at a fixed stage live on that stage. Its maps
are the actual system transitions followed by the native direct-image
composition comparison. The adjoints of the original coefficient-colimit
injections give a genuine cocone into the direct image of the limit
coefficient. We do not assert that this sheaf cocone is colimiting.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u uI vI

attribute [local instance] hasSheafifyLarge

variable {I : Type uI} [Category.{vI} I] (X : I ⥤ Scheme.{u}ᵒᵖ)
  (F : DiagramCoefficientSystem X)

/-- The actual later coefficients pushed to one fixed stage. -/
def diagramRightTail (i : I) : Under i ⥤ AbelianSheaf.{u, u + 1} (X.obj i).unop :=
  InjectiveSystem.System.rightTail (diagramAdjunctionData X)
    (diagramAdjunctionData_coherent X) F i

@[simp]
theorem diagramRightTail_obj (i : I) (a : Under i) :
    (diagramRightTail X F i).obj a =
      (directImage (X.map a.hom).unop).obj (F.obj a.right) := rfl

/-- Genuine right adjoints preserve the injectivity of the later coefficient. -/
instance diagramRightTail_obj_injective (i : I) (a : Under i)
    [Injective (F.obj a.right)] : Injective ((diagramRightTail X F i).obj a) :=
  InjectiveSystem.System.rightTail_obj_injective (diagramAdjunctionData X)
    (diagramAdjunctionData_coherent X) F i a

variable (c : Cocone X) [hF : HasColimit (coneCoefficientFunctor X c F)]

local instance rightTailCoefficientHasColimit :
    HasColimit ((diagramConeAdjunctionData X c).coefficientFunctor F) := hF

/-- The original adjoint coefficient leg, transported through the actual cone triangle. -/
def diagramRightTailLeg {i j : I} (a : i ⟶ j) :
    (directImage (X.map a).unop).obj (F.obj j) ⟶
      (directImage (c.ι.app i).unop).obj (colimit (coneCoefficientFunctor X c F)) :=
  (diagramConeAdjunctionData X c).rightTailLeg F a

/-- The original system transition and both direct-image comparisons give the
fixed-stage cocone equation for a composable pair of arrows. -/
theorem diagramRightTailLeg_step {i j k : I} (a : i ⟶ j) (b : j ⟶ k) :
    InjectiveSystem.System.rightStep (diagramAdjunctionData X) F a b ≫
        diagramRightTailLeg X F c (a ≫ b) = diagramRightTailLeg X F c a := by
  exact (diagramConeAdjunctionData X c).rightTailLeg_step F a b

/-- The same cocone equation retains a specified triangle in the original index category. -/
theorem diagramRightTailLeg_transition {i j k : I}
    (a : i ⟶ j) (b : j ⟶ k) (t : i ⟶ k) (h : a ≫ b = t) :
    InjectiveSystem.System.rightTailTransition (diagramAdjunctionData X) F a b t h ≫
        diagramRightTailLeg X F c t = diagramRightTailLeg X F c a := by
  exact (diagramConeAdjunctionData X c).rightTailLeg_transition F a b t h

/-- The canonical cocone on the actual fixed-stage right-image tail. Only
existence of the original limit coefficient colimit is needed here. -/
def diagramRightTailCocone (i : I) : Cocone (diagramRightTail X F i) :=
  (diagramConeAdjunctionData X c).rightTailCocone F (diagramAdjunctionData_coherent X) i

@[simp]
theorem diagramRightTailCocone_ι_app (i : I) (a : Under i) :
    (diagramRightTailCocone X F c i).ι.app a =
      (directImage (X.map a.hom).unop).map (diagramAdjointLeg X c F a.right) ≫
        (diagramDirectImageTriangle X c a.hom).hom.app
          (colimit (coneCoefficientFunctor X c F)) := rfl

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
