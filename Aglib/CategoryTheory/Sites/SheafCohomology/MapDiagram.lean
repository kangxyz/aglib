/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-! # Original cohomology evaluation of coefficient-map diagrams

Coefficient composition and cancellation are evaluated while all sheaves and
arrows remain variables, before selecting a geometric inverse-image diagram.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Sheaf

universe u v w e

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{e} (Sheaf J AddCommGrpCat.{w})]

/-- Original cohomology cancels the inverse of an actual coefficient iso. -/
theorem H.map_iso_inv_hom_apply {M N : Sheaf J AddCommGrpCat.{w}}
    (e : M ≅ N) (q : ℕ) (x : H.{e} N q) :
    H.map e.hom q (H.map e.inv q x) = x := by
  rw [← H.map_comp_apply, e.inv_hom_id, H.map_id_apply]

/-- The literal cohomology maps evaluate the full three-arrow coefficient
factorization, with no replacement of the original maps. -/
theorem H.map_three_factorization
    {A B C D E : Sheaf J AddCommGrpCat.{w}}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (d : A ⟶ E) (e : E ⟶ D)
    (h : a ≫ b ≫ c = d ≫ e) (q : ℕ) (x : H.{e} A q) :
    H.map e q (H.map d q x) = H.map c q (H.map b q (H.map a q x)) := by
  have he := congrArg (fun k => H.map k q x) h
  simpa only [H.map_comp_apply] using he.symm

end CategoryTheory.Sheaf
