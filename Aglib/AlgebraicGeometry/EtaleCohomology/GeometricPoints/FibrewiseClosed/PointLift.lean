/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Sites.EtalePoint
public import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-! # Actual geometric points at the standard larger sheaf-value universe -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.FibrewiseClosed

universe u

variable {T : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω]

/-- The original geometric-point fibre functor, lifted as an actual native site point
to the universe of the standard abelian-sheaf coefficients. -/
def largePoint (η : Spec (.of Ω) ⟶ T) :
    GrothendieckTopology.Point.{u + 1} (Scheme.smallEtaleTopology T) where
  fiber := (pointSmallEtale η).fiber ⋙ uliftFunctor.{u + 1}
  isCofiltered := Functor.isCofiltered_elements _
  initiallySmall := initiallySmall_of_essentiallySmall _
  jointly_surjective R hR x := by
    obtain ⟨Y, f, hf, y, hy⟩ := (pointSmallEtale η).jointly_surjective R hR x.down
    exact ⟨Y, f, hf, ULift.up y, congrArg ULift.up hy⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.FibrewiseClosed
