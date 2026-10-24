/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Slice.Adjunction
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves

/-! # Injective objects under restriction to a slice site

The original slice restriction is right adjoint to the existing exact
coproduct lower shriek. No new extension functor is used.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe v u v' u'

namespace CategoryTheory.Sheaf.SliceCohomology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (A : Type u') [Category.{v'} A] [HasCoproducts.{v} A]
  [HasFiniteLimits A] [AB4OfSize.{v} A] [HasSheafify J A]

/-- Restriction to the actual slice site preserves injective sheaves. -/
instance overPullback_preservesInjectiveObjects (U : C) :
    (J.overPullback A U).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (lowerShriekAdjunction J A U)

end CategoryTheory.Sheaf.SliceCohomology
