/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.Coefficients.PolynomialLaurent

/-! # Naturality of the geometric coefficient family

Source:
`Quillen/AlgebraicGeometry/PerfectComplexes/BoundedFlat/CoefficientBassMap.lean`
at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`.
Source SHA-256:
`d152bbfa5722c5c23c77065fc9232e258e6fc308a6398cc2ea30b51cfb11e8be`.
Selected declarations: coefficientTransformation_naturality.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.BaseChange.Coefficients
variable {R : CommRingCat.{u}} (P : Over (Spec R))

theorem coefficientMap_naturality
    {M N : Under R ⥤ Under R} (α : M ⟶ N) {a b : Under R} (u : a ⟶ b) :
    coefficientMap P (N.map u) ≫ coefficientMap P (α.app a) =
      coefficientMap P (α.app b) ≫ coefficientMap P (M.map u) := by
  rw [← coefficientMap_comp, ← coefficientMap_comp]
  exact congrArg (coefficientMap P) (α.naturality u).symm

end AlgebraicGeometry.Scheme.BaseChange.Coefficients
