/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Iso

/-! # Postcomposition of an actual isomorphism square -/

@[expose] public section
namespace CategoryTheory
variable {C : Type*} [Category* C] {A B D E T : C}

/-- A specified comparison square followed by a specified contraction keeps its original maps. -/
theorem isoSquarePostcompose (a : A ≅ B) (b : B ≅ E) (c : A ≅ D)
    (d : D ≅ E) (u : E ≅ T) (v : D ≅ T)
    (h : a ≪≫ b = c ≪≫ d) (k : d ≪≫ u = v) :
    a ≪≫ (b ≪≫ u) = c ≪≫ v := by
  rw [← Iso.trans_assoc, h, Iso.trans_assoc, k]

end CategoryTheory
