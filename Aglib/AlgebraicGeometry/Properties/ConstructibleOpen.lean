/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Spectrum.Prime.ConstructibleSet

/-! # Constructible generization-stable subsets of schemes are open

Apply the spectrum criterion on each original affine open and map its open
preimage back through the original open immersion. This is a scheme theorem,
not a statement about arbitrary Noetherian topological spaces.
-/

@[expose] public section
open Topology

namespace AlgebraicGeometry.Scheme
universe u

/-- Constructibility and generization stability imply openness on an original
scheme, by its actual affine opens and the prime-spectrum criterion. -/
theorem isOpen_of_isConstructible_of_stableUnderGeneralization
    {X : Scheme.{u}} {C : Set X} (hC : IsConstructible C)
    (hgen : StableUnderGeneralization C) : IsOpen C := by
  apply isOpen_iff_forall_mem_open.mpr
  intro x hx
  obtain ⟨V, hV, hxV, _⟩ := exists_isAffineOpen_mem_and_subset
    (show x ∈ (⊤ : X.Opens) from trivial)
  let i := hV.fromSpec
  have hxrange : x ∈ Set.range i := by
    rw [hV.range_fromSpec]
    exact hxV
  have hpre : IsConstructible (i ⁻¹' C) := i.isConstructible_preimage hC
  have hopen : IsOpen (i ⁻¹' C) :=
    PrimeSpectrum.isOpen_of_stableUnderGeneralization_of_isConstructible
      (hgen.preimage i.continuous) hpre
  refine ⟨i '' (i ⁻¹' C), Set.image_preimage_subset i C, i.isOpenEmbedding.isOpenMap _ hopen, ?_⟩
  obtain ⟨y, rfl⟩ := hxrange
  exact ⟨y, hx, rfl⟩

end AlgebraicGeometry.Scheme
