/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.NatTrans

/-! # Natural transformations from the original component and map values

Keep the two actual functors and the supplied component family. A proved
square for the original transition and its proved value as the target-functor
map construct the whole natural transformation over variable categories.
No alternative functor or desired final naturality law is assumed.
-/

@[expose] public section

namespace CategoryTheory.NatTrans

universe uI vI uV vV

variable {I : Type uI} [Category.{vI} I]
  {V : Type uV} [Category.{vV} V]
  (F G : I ⥤ V) (app : ∀ i, F.obj i ⟶ G.obj i)
  (map : ∀ {i j : I}, (i ⟶ j) → (G.obj i ⟶ G.obj j))
  (square : ∀ {i j : I} (f : i ⟶ j), F.map f ≫ app j = app i ≫ map f)
  (value : ∀ {i j : I} (f : i ⟶ j), map f = G.map f)

/-- Assemble the original component family after its actual target-map normalization. -/
def ofMapValues : NatTrans F G where
  app := app
  naturality {i _j} f :=
    (square f).trans (congrArg (fun k => app i ≫ k) (value f))

/-- The construction retains the literal original component. -/
@[simp]
theorem ofMapValues_app (i : I) :
    (ofMapValues F G app map square value).app i = app i := rfl

end CategoryTheory.NatTrans
