/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-! # Injectivity of the literal cohomology map of an isomorphism

The proof uses the original inverse coefficient map and H.map composition.
It does not convert through functorH, AddCommGrpCat or a Shrink equivalence.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Sheaf

universe u v w e

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{e} (Sheaf J AddCommGrpCat.{w})]

/-- The literal inverse coefficient map gives a left inverse on original H. -/
theorem H.map_injective_of_isIso {M N : Sheaf J AddCommGrpCat.{w}}
    (f : M ⟶ N) [IsIso f] (q : ℕ) : Function.Injective (H.map f q) := by
  intro x y hxy
  have h := congrArg (H.map (inv f) q) hxy
  rwa [← H.map_comp_apply, ← H.map_comp_apply, IsIso.hom_inv_id,
    H.map_id_apply, H.map_id_apply] at h

end CategoryTheory.Sheaf
