/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.ModuleComposite

/-! # Original coefficient cancellation in module/cohomology comparisons

The inverse coefficient map cancels the last factor of the original composite
on native cohomology values, before any geometric site is instantiated.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

universe c v a e r m h

namespace CategoryTheory.Sheaf

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{a}] [HasExt.{e} (Sheaf J AddCommGrpCat.{a})]
  {R : Type r} [Ring R] {M N : ModuleCat.{m} R}
  {H : Type h} [AddCommGroup H] [Module R H]
  {F G : Sheaf J AddCommGrpCat.{a}}

/-- Cancel the original last coefficient factor on native cohomology values. -/
theorem moduleCohomologyComposite_coefficient_inv (q : ℕ)
    (i : M ≅ N) (l : N ≃ₗ[R] H)
    (E : H ≃+ Sheaf.H.{e} F q) (β : F ≅ G) (x : M) :
    Sheaf.H.map β.inv q (moduleCohomologyComposite q i l E β x) =
      E (l (i.hom x)) := by
  rw [moduleCohomologyComposite_apply, ← Sheaf.H.map_comp_apply,
    Iso.hom_inv_id, Sheaf.H.map_id_apply]

end CategoryTheory.Sheaf
