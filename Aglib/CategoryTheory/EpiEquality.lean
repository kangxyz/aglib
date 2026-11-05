/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.CategoryTheory.EpiMono

/-! # Transport epimorphy across an already proved original-map equality -/
@[expose] public section
namespace CategoryTheory
variable {C : Type*} [Category C] {X Y : C}

theorem epi_of_map_eq (f g : X ⟶ Y) (h : f = g) (hg : Epi g) : Epi f := by
  cases h
  exact hg

end CategoryTheory
