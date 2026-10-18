/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.ProjectiveSpace.Tensor.Flat

/-! Focused consumer of the relative flatness of twists on projective space, with axiom guards. -/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules

universe u

/-- Twists of a relatively flat module are relatively flat, and every sum of twisting sheaves is
relatively flat over the base ring. -/
example {R : Type u} [CommRing R] {ι : Type u} (M : (ProjectiveSpace R ι).Modules)
    (hM : relativeFlat (toSpec R ι) M) (d : ℤ) {I : Type u} (e : I → ℤ) :
    relativeFlat (toSpec R ι)
        ((moduleTensorLeftFunctor (ProjectiveSpace R ι) (twistingSheaf R ι d)).obj M) ∧
      relativeFlat (toSpec R ι) (∐ fun i => twistingSheaf R ι (e i)) :=
  ⟨twistingTensor_relativeFlat _ M hM d, twistingCoproduct_relativeFlat R ι e⟩

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingTensor_relativeFlat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingTensor_relativeFlat

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingSheaf_relativeFlat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingSheaf_relativeFlat

/--
info: 'AlgebraicGeometry.ProjectiveSpace.twistingCoproduct_relativeFlat' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.ProjectiveSpace.twistingCoproduct_relativeFlat
