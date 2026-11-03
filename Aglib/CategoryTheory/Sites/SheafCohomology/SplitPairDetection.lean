/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.Splitting

/-! # Original cohomology classes detected by a split pair -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Sheaf

universe u v w e

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{e} (Sheaf J AddCommGrpCat.{w})]

/-- A split pair of original coefficient arrows detects zero in every original
cohomology degree. The supplied splitting identity is retained literally. -/
theorem H.eq_zero_of_split_pair
    {M N P : Sheaf J AddCommGrpCat.{w}} (f : M ⟶ N) (g : M ⟶ P)
    (r : N ⟶ M) (s : P ⟶ M) (hsplit : f ≫ r + g ≫ s = 𝟙 M)
    (q : ℕ) (x : H.{e} M q) (hf : H.map f q x = 0) (hg : H.map g q x = 0) :
    x = 0 := by
  calc
    x = H.map (𝟙 M) q x := (H.map_id_apply x).symm
    _ = 0 := by
      rw [← hsplit, H.map_add_apply, H.map_comp_apply, H.map_comp_apply,
        hf, hg, map_zero, map_zero, add_zero]

end CategoryTheory.Sheaf
