/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

example {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [Smooth f] [PreconnectedSpace X] (x : X) :
    ∃ n, SmoothOfRelativeDimension n f :=
  exists_smoothOfRelativeDimension_of_preconnected f x
