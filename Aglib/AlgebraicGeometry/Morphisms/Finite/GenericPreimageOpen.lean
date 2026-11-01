/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.FunctionField.Map
public import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Affine target neighborhoods controlling the entire finite inverse image -/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- For a finite injective dominant map, a source generic neighborhood contains
the entire inverse image of a smaller affine target generic neighborhood.
No Noetherian hypothesis is needed. Injectivity excludes other generic branches. -/
theorem exists_affine_open_generic_preimage_subset
    {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) [IsFinite f] [IsDominant f] (hf : Function.Injective f)
    (V : X.Opens) (hV : genericPoint X ∈ V)
    (W : Y.Opens) (hW : genericPoint Y ∈ W) :
    ∃ U : Y.Opens, IsAffineOpen U ∧ genericPoint Y ∈ U ∧ U ≤ W ∧ f ⁻¹ᵁ U ≤ V := by
  let B : Y.Opens := ⟨(f '' (V : Set X)ᶜ)ᶜ,
    (f.isClosedMap _ V.isOpen.isClosed_compl).isOpen_compl⟩
  have hB : genericPoint Y ∈ B := by
    rintro ⟨x, hx, he⟩
    have hxg : x = genericPoint X := hf (he.trans (map_genericPoint_of_isDominant X f).symm)
    apply hx
    change x ∈ V
    rw [hxg]
    exact hV
  obtain ⟨U, hUa, hU, hUB⟩ :=
    Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens (show genericPoint Y ∈ B ⊓ W from ⟨hB, hW⟩)
  refine ⟨U, hUa, hU, le_trans hUB inf_le_right, ?_⟩
  intro x hx
  by_contra hn
  exact (hUB hx).1 ⟨x, hn, rfl⟩

end AlgebraicGeometry.Scheme
