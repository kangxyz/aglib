/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Points.Closed
public import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
public import Mathlib.Topology.JacobsonSpace

/-! # Closed points of an open subscheme of a Jacobson scheme

The native open-embedding theorem for closed points produces an embedding of
the actual scheme-point subtypes. Its image consists precisely of the closed
target points in the original scheme map's range. No curve model is introduced.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.ClosedPoint

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [JacobsonSpace X]

/-- The actual point map of an open immersion embeds closed points when the
target is Jacobson. This hypothesis cannot be dropped for arbitrary schemes. -/
def openEmbedding : ClosedPoint U ↪ ClosedPoint X where
  toFun x := ⟨j x.val, by
    change x.val ∈ (j : U → X) ⁻¹' closedPoints X
    rw [j.isOpenEmbedding.preimage_closedPoints]
    exact x.property⟩
  inj' := by
    intro x y h
    apply Subtype.ext
    exact j.isOpenEmbedding.injective (congrArg Subtype.val h)

/-- The embedding is the original scheme map on actual points. -/
@[simp]
theorem openEmbedding_apply_val (x : ClosedPoint U) :
    (openEmbedding j x).val = j x.val := rfl

/-- Its image is exactly the closed target points belonging to the open image. -/
theorem mem_range_openEmbedding_iff (x : ClosedPoint X) :
    x ∈ Set.range (openEmbedding j) ↔ x.val ∈ Set.range j := by
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.val, rfl⟩
  · rintro ⟨y, hy⟩
    have hc : IsClosed ({y} : Set U) := by
      convert x.property.preimage j.continuous using 1
      ext z
      simp only [Set.mem_singleton_iff, Set.mem_preimage, ← hy,
        j.isOpenEmbedding.injective.eq_iff]
    exact ⟨⟨y, hc⟩, Subtype.ext hy⟩

end AlgebraicGeometry.Scheme.ClosedPoint
