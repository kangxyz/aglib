/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.RightInsertion
public import Aglib.AlgebraicGeometry.Modules.Tensor.Section


/-!
# Pullback of the original positive section insertion

The original insertion followed by the original braiding is right-unit
insertion. Its pullback is compared using the native tensor comparison
and the original pullback unit, without a new section or tensor map.
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory BraidedCategory

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The existing braided positive-section map is the original right-unit insertion. -/
theorem positiveSection_eq_rightInsertion (X : Scheme.{u}) (M N : X.Modules)
    (s : SheafOfModules.unit X.ringCatSheaf ⟶ N) :
    (positiveCartierTensorSection X N s).app M ≫ (tensorSheafBraiding X N M).hom =
      (ρ_ M).inv ≫ tensorSheafMap X (𝟙 M) s := by
  change ((λ_ M).inv ≫ (s ⊗ₘ 𝟙 M)) ≫ (β_ N M).hom =
    (ρ_ M).inv ≫ (𝟙 M ⊗ₘ s)
  rw [Category.assoc, braiding_naturality, ← Category.assoc, leftUnitor_inv_braiding]

/-- The actual positive section square commutes with the canonical tensor pullback map. -/
theorem pullback_positiveSection {X Y : Scheme.{u}} (f : X ⟶ Y) (M N : Y.Modules)
    (s : SheafOfModules.unit Y.ringCatSheaf ⟶ N) :
    (pullback f).map ((positiveCartierTensorSection Y N s).app M ≫
        (tensorSheafBraiding Y N M).hom) ≫ pullbackTensorMap f M N =
      (positiveCartierTensorSection X ((pullback f).obj N)
        ((pullbackUnitIso f).inv ≫ (pullback f).map s)).app ((pullback f).obj M) ≫
          (tensorSheafBraiding X ((pullback f).obj N) ((pullback f).obj M)).hom := by
  rw [positiveSection_eq_rightInsertion, positiveSection_eq_rightInsertion]
  exact pullback_rightInsertion f M N s

end AlgebraicGeometry.Scheme.Modules
