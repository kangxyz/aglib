/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Monoidal.Symmetric
public import Aglib.CategoryTheory.Monoidal.UnitMultiplication


/-!
# AlgebraicGeometry / Modules / Tensor / Section

Source: `RightAdjoint/Cartier.lean`.
Incoming SHA256: `9600de5300d167ece39c6d5659912637a344527ed717f35ac4f3adea465da02d`.
The original constructors, maps, universe bounds and mathematical hypotheses are retained.
-/

@[expose] public noncomputable section


open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.BraidedCategory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- The original tensor-unit inverse followed by the supplied section coefficient map. -/
public def positiveCartierTensorSection (X : Scheme.{u}) (L : X.Modules)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ L) :
    𝟭 X.Modules ⟶ moduleTensorLeftFunctor X L :=
  (SheafOfModulesOfCommRing.tensorLeftUnitIso X.sheaf).inv ≫ moduleTensorCoefficientMap X s
/-- Every component retains the original tensor-unit inverse and original coefficient map. -/
public theorem positiveCartierTensorSection_app (X : Scheme.{u}) (L M : X.Modules)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ L) :
    (positiveCartierTensorSection X L s).app M =
      (tensorSheafLeftUnit X M).inv ≫ (moduleTensorCoefficientMap X s).app M := rfl
/-- The actual associator compares insertion of the section before a tensor product. -/
public theorem positiveCartierTensorSection_tensor (X : Scheme.{u}) (L M N : X.Modules)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ L) :
    (positiveCartierTensorSection X L s).app (M ⊗ N) ≫ (α_ L M N).inv =
      (positiveCartierTensorSection X L s).app M ▷ N := by
  rw [positiveCartierTensorSection_app X L (M ⊗ N) s,
    positiveCartierTensorSection_app X L M s,
    moduleTensorCoefficientMap_app_eq_whiskerRight X s (M ⊗ N),
    moduleTensorCoefficientMap_app_eq_whiskerRight X s M,
    ← leftUnitor_eq_tensorSheafLeftUnit X (M ⊗ N),
    ← leftUnitor_eq_tensorSheafLeftUnit X M]
  change MonoidalCategory.unitMultiply (C := X.Modules) s (M ⊗ N) ≫
      (α_ L M N).inv = MonoidalCategory.unitMultiply (C := X.Modules) s M ▷ N
  rw [← MonoidalCategory.unitMultiply_whiskerRight_associator
    (C := X.Modules) s M N, Category.assoc, Iso.hom_inv_id, Category.comp_id]

end AlgebraicGeometry.Scheme.Modules
