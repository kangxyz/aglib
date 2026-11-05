/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.ModuleCoefficientSystem
public import Aglib.CategoryTheory.Sites.SheafCohomology.Continuity.InjectiveDiagram.ConeRightTail

/-! # Original native module coefficients at a scheme cone

The original adjunctions construct the actual coefficient diagram at the cone
point and its fixed-stage right-image cocones. No colimit continuity assertion
or alternative coefficient model is assumed here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule

universe u r uI vI

variable (R : Type r) [Ring R] {I : Type uI} [Category.{vI} I]
    (X : I ⥤ Scheme.{u}ᵒᵖ) (c : Cocone X)

/-- Native cone data selected by the unchanged image adjunctions. -/
def diagramConeAdjunctionData :
    (diagramAdjunctionData R X).Cone (Coefficient R c.pt.unop) :=
  InjectiveSystem.AdjunctionData.Cone.ofCocone (schemeAdjunctionData R)
    (schemeAdjunctionData_coherent R) X c

/-- Actual native coefficients and transitions at the original cone point. -/
def coneCoefficientFunctor (F : DiagramCoefficientSystem R X) :
    I ⥤ Coefficient R c.pt.unop :=
  (diagramConeAdjunctionData R X c).coefficientFunctor F

/-- The coefficient objects are the original inverse images. -/
@[simp]
theorem coneCoefficientFunctor_obj (F : DiagramCoefficientSystem R X) (i : I) :
    (coneCoefficientFunctor R X c F).obj i =
      (inverseImage R (c.ι.app i).unop).obj (F.obj i) := rfl

/-- Later native coefficients pushed to the fixed original stage. -/
def diagramRightTail (F : DiagramCoefficientSystem R X) (i : I) :
    Under i ⥤ Coefficient R (X.obj i).unop :=
  InjectiveSystem.System.rightTail (diagramAdjunctionData R X)
    (diagramAdjunctionData_coherent R X) F i

variable (F : DiagramCoefficientSystem R X)
    [hF : HasColimit (coneCoefficientFunctor R X c F)]

local instance rightTailCoefficientHasColimit :
    HasColimit ((diagramConeAdjunctionData R X c).coefficientFunctor F) := hF

/-- Original adjoint legs define the actual right-image cocone. -/
def diagramRightTailCocone (i : I) : Cocone (diagramRightTail R X F i) :=
  (diagramConeAdjunctionData R X c).rightTailCocone F
    (diagramAdjunctionData_coherent R X) i

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.NativeModule
