/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.AdditiveComposite
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-! # Original module comparisons with original sheaf cohomology

The complete comparison retains the original module isomorphism, linear and
additive comparisons, and coefficient isomorphism. Its last maps are native
`Sheaf.H.map`, on the original cohomology groups. Categorical cohomology-object
metadata is normalized here, before any geometric site is instantiated.
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

/-- Assemble the original module comparison and original coefficient map on H,
without exposing categorical `functorH.obj` carriers to geometric consumers. -/
def moduleCohomologyComposite (q : ℕ) (i : M ≅ N) (l : N ≃ₗ[R] H)
    (a : H ≃+ Sheaf.H.{e} F q) (b : F ≅ G) : M ≃+ Sheaf.H.{e} G q := by
  let E := Iso.moduleAdditiveComposite i l a
    ((Sheaf.functorH.{e, a, v, c} J q).mapIso b)
  exact
    { toFun := fun x => Sheaf.H.map b.hom q (a (l (i.hom x)))
      invFun := fun y => i.inv (l.symm (a.symm (Sheaf.H.map b.inv q y)))
      left_inv := E.left_inv
      right_inv := E.right_inv
      map_add' := E.map_add }

/-- Evaluation is the literal original cohomology coefficient map. -/
theorem moduleCohomologyComposite_apply (q : ℕ) (i : M ≅ N) (l : N ≃ₗ[R] H)
    (a : H ≃+ Sheaf.H.{e} F q) (b : F ≅ G) (x : M) :
    moduleCohomologyComposite q i l a b x =
      Sheaf.H.map b.hom q (a (l (i.hom x))) := rfl

end CategoryTheory.Sheaf
