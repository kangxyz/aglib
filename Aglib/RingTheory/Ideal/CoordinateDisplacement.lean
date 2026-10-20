/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Tactic.Ring

/-!
# Coordinate ideals under displacement inside a fixed ideal


Source: `R5Lab.Aglib.RingTheory.Ideal.CoordinateDisplacement`.
Packet SHA-256:
`7e84d20773ec3171e53f49079043565e017cce3d5fda79e6401fdf43d9bcda64`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [CommRing R]

/-- A displacement in the original base ideal preserves the coordinate-centre
ideal; this is an equality of actual ideals, before any local-ring assertion. -/
theorem coordinate_center_ideal_eq (I : Ideal R) (X Y r₀ t₀ r t : R)
    (hr : r - r₀ ∈ I) (ht : t - t₀ ∈ I) :
    I ⊔ Ideal.span {X - r₀, Y - t₀} = I ⊔ Ideal.span {X - r, Y - t} := by
  have hle (r₀ t₀ r t : R) (hr : r - r₀ ∈ I) (ht : t - t₀ ∈ I) :
      I ⊔ Ideal.span {X - r₀, Y - t₀} ≤ I ⊔ Ideal.span {X - r, Y - t} := by
    have hi : I ≤ I ⊔ Ideal.span {X - r, Y - t} := le_sup_left
    have hj : Ideal.span {X - r, Y - t} ≤ I ⊔ Ideal.span {X - r, Y - t} := le_sup_right
    refine sup_le le_sup_left (Ideal.span_le.mpr ?_)
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · have he : X - r₀ = (X - r) + (r - r₀) := by ring
      rw [he]
      exact (I ⊔ Ideal.span {X - r, Y - t}).add_mem
        (hj (Ideal.subset_span (by simp))) (hi hr)
    · have he : Y - t₀ = (Y - t) + (t - t₀) := by ring
      rw [he]
      exact (I ⊔ Ideal.span {X - r, Y - t}).add_mem
        (hj (Ideal.subset_span (by simp))) (hi ht)
  exact le_antisymm (hle _ _ _ _ hr ht) (hle _ _ _ _
    (by simpa only [neg_sub] using I.neg_mem hr)
    (by simpa only [neg_sub] using I.neg_mem ht))

end Ideal
