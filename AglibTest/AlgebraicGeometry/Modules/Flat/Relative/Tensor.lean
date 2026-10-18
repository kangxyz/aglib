/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Modules.Flat.Relative.Tensor

/-! Focused consumer of relative flatness of tensor products with locally trivial sheaves, with an
axiom guard. -/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

example {X Y : Scheme.{u}} (f : X ⟶ Y) (L M : X.Modules)
    (hL : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (L.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    (hM : Scheme.Modules.relativeFlat f M) :
    Scheme.Modules.relativeFlat f ((Scheme.Modules.moduleTensorLeftFunctor X L).obj M) :=
  Scheme.Modules.relativeFlat_tensor_of_locallyTrivial f L M hL hM

/--
info: 'AlgebraicGeometry.Scheme.Modules.relativeFlat_tensor_of_locallyTrivial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Modules.relativeFlat_tensor_of_locallyTrivial
