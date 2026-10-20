/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.Map

/-! Compatibility of actual function-field maps with stalk localization and units. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u
variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (f : X ⟶ Y) [IsDominant f]

/-- Pullback on actual generic stalks commutes with every point-stalk localization. -/
theorem functionFieldMap_stalk (x : X) (a : Y.presheaf.stalk (f x)) :
    Scheme.functionFieldMap f (algebraMap (Y.presheaf.stalk (f x)) Y.functionField a) =
      algebraMap (X.presheaf.stalk x) X.functionField (f.stalkMap x a) := by
  have he : Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial) ≫
      Y.presheaf.stalkSpecializes (specializes_of_eq (Scheme.map_genericPoint_of_isDominant X f)) ≫
        f.stalkMap (genericPoint X) =
      f.stalkMap x ≫ X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) := by
    rw [← Category.assoc, TopCat.Presheaf.stalkSpecializes_comp]
    exact f.stalkSpecializes_stalkMap _ x ((genericPoint_spec X).specializes trivial)
  exact congrArg (fun h : Y.presheaf.stalk (f x) ⟶ X.functionField => h a) he

/-- Pullback on units uses the same actual function-field map. -/
def functionFieldUnitMap : Y.functionFieldˣ →* X.functionFieldˣ :=
  Units.map (Scheme.functionFieldMap f).toMonoidHom

end AlgebraicGeometry.Scheme

/- Migration source: R5Lab/Aglib/AlgebraicGeometry/Morphisms/Finite/ClosedPoints.lean,
SHA-256 4771433b7e42eaa04fa35c9751f3164241404a6daf04e09f2b5e4834cf6f5a9a.
No finite-morphism or Noetherian hypothesis occurs in these declarations. -/
