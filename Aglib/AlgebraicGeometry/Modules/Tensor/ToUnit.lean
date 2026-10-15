/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Sections
public import Aglib.AlgebraicGeometry.Modules.StructureSheaf.Sections
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.RightUnit
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas

/-!
# Tensor maps induced by an arrow to the structure module

An actual arrow `f : L ⟶ O_X` induces the canonical transformation `L ⊗ - ⟶ Id`.
No local freeness or rank assumption on `L` is required. The section, restriction and
unit equations identify the actual coefficient tensor map and unitors.

Source: delivered `PerfectComplexes/ProjectiveLine/LineCoordinateTensor.lean`
(moduleLineCoordinate, moduleLineCoordinate_section, moduleLineCoordinate_restrict)
and `LineCoordinateUnit.lean` (lineCoordinate_unitors, moduleLineCoordinate_unit).
The scalar-specific equation and perfect-complex specializations remain downstream.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry Opposite SheafOfModulesOfCommRing

namespace AlgebraicGeometry.Scheme.Modules

/-- The coefficient tensor map induced by `f`, followed by the canonical left unitor. -/
def tensorToUnit {X : Scheme.{u}} {L : X.Modules}
    (f : L ⟶ SheafOfModules.unit X.ringCatSheaf) :
    moduleTensorLeftFunctor X L ⟶ 𝟭 X.Modules :=
  moduleTensorCoefficientMap X f ≫ (tensorLeftUnitIso X.sheaf).hom

/-- The tensor map sends a pure tensor to the scalar image of its first factor times the second. -/
theorem tensorToUnit_section {X : Scheme.{u}} {L : X.Modules}
    (f : L ⟶ SheafOfModules.unit X.ringCatSheaf) (M : X.Modules) (U : X.Opens)
    (a : Γ(L, U)) (m : Γ(M, U)) :
    ((tensorToUnit f).app M).app U (moduleTensorSection X L M U a m) =
      (show Γ(X, U) from f.app U a) • m := by
  change ((tensorLeftUnitIso X.sheaf).hom.app M).val.app (op U)
    (((moduleTensorCoefficientMap X f).app M).app U
      (moduleTensorSection X L M U a m)) = _
  rw [moduleTensorCoefficientMap_section]
  exact congrArg (fun g => g.app (op U) ((f.app U a) ⊗ₜ[Γ(X, U)] m))
    (associatedSheafUnit_tensorLeftUnitIso X.sheaf M)

/-- Open restriction retains the canonical tensor and structure-module comparison maps. -/
theorem tensorToUnit_restrict {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] {L : X.Modules}
    (f : L ⟶ SheafOfModules.unit X.ringCatSheaf) (M : X.Modules) :
    (tensorRestrictionIso j L M).hom ≫
        (Scheme.Modules.restrictFunctor j).map ((tensorToUnit f).app M) =
      (tensorToUnit ((Scheme.Modules.restrictFunctor j).map f ≫
        (Scheme.Modules.restrictUnitIso j).hom)).app (M.restrict j) := by
  apply moduleTensor_hom_ext
  intro V a m
  change ((tensorToUnit f).app M).app (j ''ᵁ V)
    ((tensorRestrictionIso j L M).hom.app V
      (moduleTensorSection U (L.restrict j) (M.restrict j) V a m)) = _
  rw [tensorRestrictionIso_section]
  erw [tensorToUnit_section, tensorToUnit_section]
  let s : Γ(X, j ''ᵁ V) := f.app (j ''ᵁ V) a
  change s • (show Γ(M, j ''ᵁ V) from m) =
    (j.appIso V).inv.hom ((j.appIso V).hom.hom s) • (show Γ(M, j ''ᵁ V) from m)
  rw [← CommRingCat.comp_apply, Iso.hom_inv_id]
  rfl

/-- The actual left and right tensor unitors agree at the structure module. -/
theorem tensorUnitors_eq (X : Scheme.{u}) :
    (tensorLeftUnitIso X.sheaf).hom.app (SheafOfModules.unit X.ringCatSheaf) =
      (tensorRightUnitIso X.sheaf).hom.app (SheafOfModules.unit X.ringCatSheaf) := by
  exact congrArg
    (fun f => (associatedSheaf X.sheaf).map f ≫
      (PresheafOfModules.sheafificationAdjunction (R := X.ringCatSheaf) (𝟙 _)).counit.app
        (SheafOfModules.unit X.ringCatSheaf))
    (CategoryTheory.MonoidalCategory.unitors_equal
      (C := PresheafOfModulesOfCommRing.{u} X.sheaf.obj))

/-- At the unit coefficient, the tensor transformation is the right unitor followed by `f`. -/
theorem tensorToUnit_unit {X : Scheme.{u}} {L : X.Modules}
    (f : L ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (tensorToUnit f).app (SheafOfModules.unit X.ringCatSheaf) =
      (tensorRightUnitIso X.sheaf).hom.app L ≫ f := by
  change ((tensorFunctor X.sheaf).map f).app _ ≫
    (tensorLeftUnitIso X.sheaf).hom.app _ = _
  rw [tensorUnitors_eq]
  exact (tensorRightUnitIso X.sheaf).hom.naturality f

end AlgebraicGeometry.Scheme.Modules
