/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Morphisms.Etale.At
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-! # Generizations in the image of the original etale locus

The open image of an actual etale source neighborhood contains every
generization of the original image point. Its preimage remains in that same
original neighborhood. No finiteness or global flatness premise is required.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- A generization of the image of an etale point has an etale preimage,
constructed inside the original open source neighborhood. -/
theorem etaleAt.exists_preimage_of_specializes
    {Z X : Scheme.{u}} {f : Z ⟶ X} {z : Z} (h : f.etaleAt z)
    {x : X} (hx : x ⤳ f z) : ∃ z' : Z, f z' = x ∧ f.etaleAt z' := by
  obtain ⟨U, hz, hU⟩ := h
  let : Etale (U.ι ≫ f) := hU
  have hopen : IsOpen (Set.range (U.ι ≫ f)) :=
    (U.ι ≫ f).isOpenMap.isOpen_range
  have hmem : f z ∈ Set.range (U.ι ≫ f) := ⟨⟨z, hz⟩, rfl⟩
  obtain ⟨w, hw⟩ := hx.mem_open hopen hmem
  exact ⟨U.ι w, hw, U, w.property, hU⟩

end AlgebraicGeometry.Scheme.Hom
