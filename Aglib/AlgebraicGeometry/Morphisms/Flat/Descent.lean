/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Flat.Descent
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Flat morphisms descend along fpqc base change -/

@[expose] public section


open CategoryTheory

namespace AlgebraicGeometry

universe u

/-- Native fpqc descent for flat scheme morphisms. The affine and local
assembly is the existing scheme constructor applied to tensor-product
descent for the actual ring maps. -/
instance Flat.descendsAlong_surjective_inf_flat_inf_quasiCompact :
    MorphismProperty.DescendsAlong (@Flat.{u}) (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat RingHom.Flat.codescendsAlong_faithfullyFlat

end AlgebraicGeometry
