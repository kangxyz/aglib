/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed ranges after pullback through a closed embedding

The actual pullback projections identify the inverse image of the range of
a composite with the image of the inverse image of its first factor. When
the second factor is closed, closedness can be checked on that pullback.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Pullback

variable {X C Y S : Scheme.{u}} (a : X ⟶ C) (e : C ⟶ Y) (b : S ⟶ Y)

/-- The original pullback projections identify the range of a composite. -/
theorem preimage_range_comp_eq_image :
    b ⁻¹' Set.range (a ≫ e) =
      pullback.fst b e '' (pullback.snd b e ⁻¹' Set.range a) := by
  ext x
  constructor
  · rintro ⟨z, hz⟩
    change e (a z) = b x at hz
    obtain ⟨y, hy₁, hy₂⟩ := exists_preimage_pullback x (a z) hz.symm
    exact ⟨y, ⟨z, hy₂.symm⟩, hy₁⟩
  · rintro ⟨y, ⟨z, hz⟩, hxy⟩
    refine ⟨z, ?_⟩
    change e (a z) = b x
    calc
      e (a z) = e (pullback.snd b e y) := congrArg e hz
      _ = b (pullback.fst b e y) :=
        congrArg (fun k : pullback b e ⟶ Y => k y) (pullback.condition (f := b) (g := e)).symm
      _ = b x := congrArg b hxy

/-- Closedness of a pulled range may be tested inside the pullback of a
specified closed embedding. -/
theorem isClosed_preimage_range_comp_iff [IsClosedImmersion e] :
    IsClosed (b ⁻¹' Set.range (a ≫ e)) ↔
      IsClosed (pullback.snd b e ⁻¹' Set.range a) := by
  rw [preimage_range_comp_eq_image]
  exact (pullback.fst b e).isClosedEmbedding.isClosed_iff_image_isClosed.symm

end AlgebraicGeometry.Scheme.Pullback
