/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Aglib.Algebra.Category.ModuleCat.ForgetAction
public import Aglib.CategoryTheory.Preadditive.ScalarDiagram
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Abelian

/-! # Constant cohomology with original noncommutative left scalars

The actual constant abelian sheaf and its cohomology are unchanged. Only the
original scalar action is recorded on their carriers and coefficient maps.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace ModuleCat.Sheaf
universe u v r e
variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type r) [Ring R]
  [HasSheafify J AddCommGrpCat.{max u v}]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{max u v})]

/-- The original constant-sheaf cohomology applied to coefficient diagrams. -/
abbrev constantCohomologyDiagramFunctor (q : ℕ) :=
  (Functor.whiskeringRight (ModuleCat.{max u v} R)
    AddCommGrpCat.{max u v} AddCommGrpCat.{e}).obj
      (constantSheaf J AddCommGrpCat.{max u v} ⋙ CategoryTheory.Sheaf.functorH J q)

/-- The original constant cohomology with its possibly noncommutative left action. -/
def constantCohomologyOfRing (q : ℕ) : ModuleCat.{max u v} R ⥤ ModuleCat.{e} R :=
  (constantCohomologyDiagramFunctor J R q).coefficientModuleDiagram
    (forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v})
    (ModuleCat.forgetScalarAction R)

/-- Addition of actual coefficient maps is unchanged by the scalar lift. -/
instance constantCohomologyOfRing_additive (q : ℕ) :
    (constantCohomologyOfRing J R q).Additive where
  map_add := by
    intro M N f g
    ext x
    change (constantSheaf J AddCommGrpCat.{max u v} ⋙
        CategoryTheory.Sheaf.functorH J q).map
      (((forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).map f) +
        ((forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).map g)) x = _
    rw [Functor.map_add]
    rfl

/-- The whole underlying constant cohomology functor and all its maps are unchanged. -/
def constantCohomologyOfRingForgetIso (q : ℕ) :
    constantCohomologyOfRing J R q ⋙ forget₂ (ModuleCat.{e} R) AddCommGrpCat.{e} ≅
      forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v} ⋙
        constantSheaf J AddCommGrpCat.{max u v} ⋙ CategoryTheory.Sheaf.functorH J q :=
  Iso.refl _

end ModuleCat.Sheaf
