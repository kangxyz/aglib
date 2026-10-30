/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.RationalPoint.Unramified

/-! # Direct lower consumer of the preserved cotangent-unramifiedness interface -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory
open AlgebraicGeometry.Scheme.OverField

universe u

attribute [local instance] Over.cartesianMonoidalCategory

example {k : Type u} [Field k] {X : FScheme k}
    (x : 𝟙_ (FScheme k) ⟶ X) (f : X ⟶ X) (h : x ≫ f = x)
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType f.left]
    (hc : Function.Surjective (Cotangent.map x x f h)) :
    (Cotangent.localMap x x f h).FormallyUnramified :=
  Cotangent.localMap_formallyUnramified_of_surjective x f h hc
