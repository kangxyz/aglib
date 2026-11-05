/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-! # An original cohomology representative through an actual coefficient iso

The inverse-image representative and its complete return equation are proved
before any geometric coefficient map or transfer is substituted. Only literal
H.map, its inverse map and composition are used, without functorH or a second
cohomology realization.
-/

@[expose] public noncomputable section

namespace CategoryTheory.Sheaf

universe u v w e t

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{w}] [HasExt.{e} (Sheaf J AddCommGrpCat.{w})]

/-- Construct the actual inverse representative and prove its complete return
along the specified original function. No surjectivity certificate is input. -/
theorem H.exists_iso_representative_return
    {M N : Sheaf J AddCommGrpCat.{w}} (f : M ⟶ N) [IsIso f] (q : ℕ)
    {A : Type t} (r : H.{e} N q → A) (a : A)
    (z : H.{e} N q) (hz : r z = a) :
    ∃ x : H.{e} M q, r (H.map f q x) = a := by
  refine ⟨H.map (inv f) q z, ?_⟩
  rw [← H.map_comp_apply, IsIso.inv_hom_id, H.map_id_apply]
  exact hz

end CategoryTheory.Sheaf
