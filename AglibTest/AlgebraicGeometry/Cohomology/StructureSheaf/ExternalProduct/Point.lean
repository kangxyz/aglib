/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.ExternalProduct.Point

/-! Point evaluation uses no flatness assumption on the rational point. -/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open AlgebraicGeometry.Scheme.OverField AlgebraicGeometry.Scheme.Cohomology

attribute [local instance] Over.cartesianMonoidalCategory

universe u
variable {k : Type u} [Field k] (X Y : FScheme k)

example (e : 𝟙_ (FScheme k) ⟶ X) (p q : ℕ)
    (x : Scheme.structureCohomology k X (p + 1)) (y : Scheme.structureCohomology k Y q) :
    structureCohomologyPullbackLinear (lift (toUnit Y ≫ e) (𝟙 Y)) (p + 1 + q)
      (structureExternalCup X Y rfl x y) = 0 :=
  structureExternalCup_point_left_succ X Y e rfl x y

example [IsProper Y.hom] [GeometricallyIntegral Y.hom]
    (e : 𝟙_ (FScheme k) ⟶ Y) (n : ℕ)
    (x : Scheme.structureCohomology k X n) (y : Scheme.structureCohomology k Y 0) :
    structureCohomologyPullbackLinear (lift (𝟙 X) (toUnit X ≫ e)) n
      (structureExternalCup X Y (Nat.add_zero n) x y) =
        (structureH0ScalarEquiv Y).symm y • x :=
  structureExternalCup_point_right_zero X Y e x y
