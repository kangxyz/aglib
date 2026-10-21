/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.ChartPullbackCoordinateSections

/-! # Shared original affine-chart unit equations

The regular unit-equation predicate retains the exact coordinate unit tensor
and original restricted geometric unit. Suppliers and concrete consumers can
share this proposition head without reconstructing the evaluated comparison.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {X Z : Scheme.{u}} (p : Z ⟶ X)
  (j : Spec (CommRingCat.of R) ⟶ X) [IsOpenImmersion j]
  (c : Spec (CommRingCat.of S) ⟶ Z) [IsOpenImmersion c]
  (H : c ≫ p = Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫ j)
  (M : X.Modules) [M.IsQuasicoherent]

local notation "φ" => CommRingCat.ofHom (algebraMap R S)

/-- The coordinate unit tensor equals the original pullback-unit section on
the supplied actual affine chart. -/
def chartPullbackCoordinateUnitEquation {N : ModuleCat.{u} R}
    (e : moduleSpecΓFunctor.obj (M.restrict j) ≅ N) (n : N) : Prop :=
  (chartPullbackCoordinatesIso p j c H M e).inv ((1 : S) ⊗ₜ[R] n) =
    (Nonflat.chartCoefficient p j c (Spec.map φ) H.symm
      ((pullbackPushforwardAdjunction p).unit.app M)).app ⊤ (e.inv n)

/-- The original affine-chart coordinate comparison satisfies the shared
unit-equation predicate, with no additional hypothesis on the geometry. -/
theorem chartPullbackCoordinateUnitEquation_of_coordinates {N : ModuleCat.{u} R}
    (e : moduleSpecΓFunctor.obj (M.restrict j) ≅ N) (n : N) :
    chartPullbackCoordinateUnitEquation p j c H M e n := by
  exact chartPullbackCoordinatesIso_inv_one_tmul p j c H M e n

end AlgebraicGeometry.Scheme.Modules
