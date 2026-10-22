/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Compactification.Boundary.ProjectedCentres

/-! # The exact overlap of a boundary complement with its protected open -/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Compactification

/-- The ambient complement of the closure of a closed subset of an open. -/
def boundaryComplementOpen {Y : Scheme.{u}} (V : Y.Opens) (F : Closeds V.toScheme) :
    Y.Opens := ⟨(closure (V.ι '' (F : Set V.toScheme)))ᶜ, isClosed_closure.isOpen_compl⟩

/-- Its overlap with the original open is exactly the complement of the
specified closed subset, including nonreduced schemes. -/
theorem preimage_boundaryComplementOpen {Y : Scheme.{u}}
    (V : Y.Opens) (F : Closeds V.toScheme) :
    V.ι ⁻¹ᵁ boundaryComplementOpen V F = F.compl := by
  apply SetLike.coe_injective
  ext x
  change ¬ V.ι x ∈ closure (V.ι '' (F : Set V.toScheme)) ↔ x ∉ (F : Set V.toScheme)
  have hx : V.ι x ∈ closure (V.ι '' (F : Set V.toScheme)) ↔
      V.ι x ∈ V.ι '' (F : Set V.toScheme) := by
    constructor
    · intro h
      have hh : V.ι x ∈ closure (V.ι '' (F : Set V.toScheme)) ∩ (V : Set Y) :=
        ⟨h, x.property⟩
      rwa [closure_image_closed_inter_open V F] at hh
    · intro h
      exact (subset_closure (s := V.ι '' (F : Set V.toScheme))) h
  rw [hx]
  apply not_congr
  constructor
  · rintro ⟨y, hy, he⟩
    exact V.ι.isOpenEmbedding.injective he ▸ hy
  · intro hy
    exact ⟨x, hy, rfl⟩

/-- In a base-changed open, the closed subset is the literal inverse image
of its old image. This is an equality of underlying sets, not a
base-change identity for scheme-theoretic images. -/
theorem preimage_open_image_closed {Y Z : Scheme.{u}} (β : Z ⟶ Y)
    (V : Y.Opens) (F : Closeds V.toScheme) :
    β ⁻¹' (V.ι '' (F : Set V.toScheme)) =
      (β ⁻¹ᵁ V).ι '' ((β ∣_ V) ⁻¹' (F : Set V.toScheme)) := by
  ext z
  constructor
  · rintro ⟨y, hy, he⟩
    have hz : z ∈ β ⁻¹ᵁ V := by
      change β z ∈ V
      rw [← he]
      exact y.property
    refine ⟨⟨z, hz⟩, ?_, rfl⟩
    have hh : (β ∣_ V) ⟨z, hz⟩ = y := by
      apply V.ι.isOpenEmbedding.injective
      exact (morphismRestrict_base_coe β V ⟨z, hz⟩).trans he.symm
    change (β ∣_ V) ⟨z, hz⟩ ∈ (F : Set V.toScheme)
    rwa [hh]
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(β ∣_ V) z, hz, ?_⟩
    exact morphismRestrict_base_coe β V z

end AlgebraicGeometry.Scheme.Compactification
