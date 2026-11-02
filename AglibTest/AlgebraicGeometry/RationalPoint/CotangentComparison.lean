/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalPoint.CotangentComparison

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.Scheme.OverField

universe u

attribute [local instance] Over.cartesianMonoidalCategory

example {k : Type u} [Field k] {X Y : FScheme k}
    (x : 𝟙_ (FScheme k) ⟶ X) (y : 𝟙_ (FScheme k) ⟶ Y)
    (f : X ⟶ Y) (h : x ≫ f = y) [IsOpenImmersion f.left] :
    Function.Bijective (Cotangent.map x y f h) :=
  (Cotangent.equivOfIsOpenImmersion x y f h).bijective
