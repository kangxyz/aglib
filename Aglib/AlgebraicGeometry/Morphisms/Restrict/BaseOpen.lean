/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # The original base-open domain under the native pullback -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- A domain lying over the original base open retains that exact property
on its native pullback, with no replacement open subscheme. -/
theorem range_pullback_of_baseOpen
    {X U S T : Scheme.{u}} (p : X ⟶ S) (b : T ⟶ S) (j : U ⟶ X)
    (W : S.Opens) (hj : Set.range j = p ⁻¹' (W : Set S)) :
    Set.range (pullback.snd j (pullback.fst p b)) =
      (pullback.snd p b) ⁻¹' (b ⁻¹' (W : Set S)) := by
  rw [Scheme.Pullback.range_snd, hj]
  ext x
  change p (pullback.fst p b x) ∈ W ↔ b (pullback.snd p b x) ∈ W
  have he := congrArg (fun f : pullback p b ⟶ S => f x) (pullback.condition (f := p) (g := b))
  change p (pullback.fst p b x) = b (pullback.snd p b x) at he
  rw [he]

end AlgebraicGeometry.Scheme.Hom
