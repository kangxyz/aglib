/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.ToUnit
public import Aglib.AlgebraicGeometry.Modules.Complex.Tensor
public import Mathlib.Algebra.Homology.Additive

/-!
# Tensor maps to the unit on ordinary module-sheaf complexes

The canonical transformation induced by an actual arrow `L ⟶ O_X` is applied degreewise.
Its value on a unit single is the actual single map, through the canonical single/tensor
comparison and right unitor. No boundedness, perfectness or local-freeness premise is used.

Source: delivered `PerfectComplexes/ProjectiveLine/LineCoordinateTensor.lean`
(complexLineCoordinate, complexLineCoordinate_f) and `LineCoordinateSingle.lean`
(unitCoefficientSingleIso, complexLineCoordinate_unit_single).
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry SheafOfModulesOfCommRing

namespace AlgebraicGeometry.Scheme.Modules.Complex

/-- The canonical tensor-to-unit map applied degreewise to ordinary integer complexes. -/
def tensorToUnit {X : Scheme.{u}} {L : X.Modules}
    (f : L ⟶ SheafOfModules.unit X.ringCatSheaf) :
    tensorLeft L ⟶ 𝟭 (CochainComplex X.Modules ℤ) :=
  (Scheme.Modules.tensorToUnit f).mapHomologicalComplex (.up ℤ) ≫
    (Functor.mapHomologicalComplexIdIso X.Modules (.up ℤ)).hom

/-- Every component is the actual sheaf tensor-to-unit map on that degree. -/
theorem tensorToUnit_f {X : Scheme.{u}} {L : X.Modules}
    (f : L ⟶ SheafOfModules.unit X.ringCatSheaf) (K : CochainComplex X.Modules ℤ) (n : ℤ) :
    ((tensorToUnit f).app K).f n = (Scheme.Modules.tensorToUnit f).app (K.X n) := by
  change (Scheme.Modules.tensorToUnit f).app (K.X n) ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- Tensoring a single of the unit is the corresponding single of the coefficient sheaf. -/
def tensorLeftSingleUnitIso (X : Scheme.{u}) (L : X.Modules) (n : ℤ) :
    (tensorLeft L).obj
      ((CochainComplex.singleFunctor X.Modules n).obj
        (SheafOfModules.unit X.ringCatSheaf)) ≅
      (CochainComplex.singleFunctor X.Modules n).obj L :=
  (HomologicalComplex.singleMapHomologicalComplex
      (moduleTensorLeftFunctor X L) (.up ℤ) n).app
        (SheafOfModules.unit X.ringCatSheaf) ≪≫
    (CochainComplex.singleFunctor X.Modules n).mapIso ((tensorRightUnitIso X.sheaf).app L)

/-- On the actual unit single, the tensor transformation is the actual single map of `f`. -/
theorem tensorToUnit_single {X : Scheme.{u}} {L : X.Modules}
    (f : L ⟶ SheafOfModules.unit X.ringCatSheaf) (n : ℤ) :
    (tensorToUnit f).app
        ((CochainComplex.singleFunctor X.Modules n).obj
          (SheafOfModules.unit X.ringCatSheaf)) =
      (tensorLeftSingleUnitIso X L n).hom ≫
        (CochainComplex.singleFunctor X.Modules n).map f := by
  change ((Scheme.Modules.tensorToUnit f).mapHomologicalComplex (.up ℤ)).app
      ((HomologicalComplex.single X.Modules (.up ℤ) n).obj
        (SheafOfModules.unit X.ringCatSheaf)) ≫
      (Functor.mapHomologicalComplexIdIso X.Modules (.up ℤ)).hom.app _ = _
  rw [HomologicalComplex.natTransMapHomologicalComplex_app_single_obj,
    HomologicalComplex.singleMapHomologicalComplex_id_inv_app]
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [Scheme.Modules.tensorToUnit_unit, Functor.map_comp]
  simp only [tensorLeftSingleUnitIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  erw [Category.comp_id]
  rfl

end AlgebraicGeometry.Scheme.Modules.Complex
