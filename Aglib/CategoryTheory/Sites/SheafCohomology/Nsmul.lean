/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Multiplication on original sheaf cohomology

The additive cohomology functor transports multiplication on coefficients to multiplication
on the original Ext cohomology group, as an equality of homomorphisms before evaluation.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Sheaf

universe u v a w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{a}] [HasExt.{w} (Sheaf J AddCommGrpCat.{a})]

/-- Multiplication on coefficients induces the native multiplication homomorphism. -/
theorem H.map_nsmul_id (F : Sheaf J AddCommGrpCat.{a}) (q n : ℕ) :
    H.map (n • 𝟙 F) q = nsmulAddMonoidHom (α := H.{w} F q) n := by
  ext x
  change ((functorH J q).map (n • 𝟙 F)) x = n • x
  rw [Functor.map_nsmul, Functor.map_id]
  rfl

/-- Evaluation of the whole multiplication identity. -/
theorem H.map_nsmul_id_apply (F : Sheaf J AddCommGrpCat.{a}) (q n : ℕ) (x : H.{w} F q) :
    H.map (n • 𝟙 F) q x = n • x :=
  DFunLike.congr_fun (H.map_nsmul_id F q n) x

end CategoryTheory.Sheaf
