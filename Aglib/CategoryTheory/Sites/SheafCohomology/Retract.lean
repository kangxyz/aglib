/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Retract

/-! # Original cohomology detects classes through actual coefficient retracts -/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Sheaf

universe u v w e

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{e} (Sheaf J AddCommGrpCat.{w})]

/-- No acyclicity or injectivity of a forgotten coefficient is required:
cohomology preserves the literal retraction equation. -/
theorem H.map_injective_of_retract {M N : Sheaf J AddCommGrpCat.{w}}
    (r : Retract M N) (q : ℕ) : Function.Injective (H.map r.i q) := by
  intro x y hxy
  have h := congrArg (H.map r.r q) hxy
  rwa [← H.map_comp_apply, ← H.map_comp_apply, r.retract,
    H.map_id_apply, H.map_id_apply] at h

end CategoryTheory.Sheaf
