/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantCoefficients
public import Aglib.CategoryTheory.Linear.ModuleValued
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic

/-!
# Canonical constant-ring scalars on original sheaf cohomology

The original additive `Sheaf.H` of a native `ModuleCat`-valued sheaf carries
its coefficient-ring action: multiplication by a scalar is the original
cohomology map of scalar multiplication on that sheaf. Coefficient maps remain
literal original `Sheaf.H.map` functions and are linear. The same construction
on constant abelian sheaves retains the original constant-sheaf functor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace ModuleCat.Sheaf

universe u v r e

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (R : Type r) [CommRing R]
  [HasSheafify J AddCommGrpCat.{max u v}]
  [HasExt.{e} (Sheaf J AddCommGrpCat.{max u v})]

attribute [local instance] hasSheafify

instance underlying_additive : (underlying R J).Additive where
  map_add := by
    intro X Y f g
    ext U x
    rfl

/-- The original underlying-abelian cohomology, with its canonical coefficient scalars. -/
def cohomology (q : ℕ) :
    Sheaf J (ModuleCat.{max u v} R) ⥤ ModuleCat.{e} R :=
  Functor.moduleValued R (underlying R J ⋙ CategoryTheory.Sheaf.functorH J q)

/-- The coefficient action on the unchanged original cohomology carrier. -/
abbrev cohomologyModule (M : Sheaf J (ModuleCat.{max u v} R)) (q : ℕ) :
    Module R (CategoryTheory.Sheaf.H.{e} ((underlying R J).obj M) q) :=
  Functor.moduleObj R (underlying R J ⋙ CategoryTheory.Sheaf.functorH J q) M

attribute [local instance] cohomologyModule

/-- Scalar multiplication is the original cohomology map of the actual scalar morphism. -/
theorem cohomology_smul (M : Sheaf J (ModuleCat.{max u v} R)) (q : ℕ)
    (r : R) (x : CategoryTheory.Sheaf.H.{e} ((underlying R J).obj M) q) :
    r • x = CategoryTheory.Sheaf.H.map ((underlying R J).map (r • 𝟙 M)) q x := rfl

/-- The module-valued functor has the literal original cohomology coefficient map. -/
@[simp]
theorem cohomology_map_apply {M N : Sheaf J (ModuleCat.{max u v} R)}
    (f : M ⟶ N) (q : ℕ)
    (x : CategoryTheory.Sheaf.H.{e} ((underlying R J).obj M) q) :
    (cohomology J R q).map f x =
      CategoryTheory.Sheaf.H.map ((underlying R J).map f) q x := rfl

instance cohomology_additive (q : ℕ) : (cohomology J R q).Additive :=
  inferInstanceAs (Functor.moduleValued R
    (underlying R J ⋙ CategoryTheory.Sheaf.functorH J q)).Additive

instance cohomology_linear (q : ℕ) : (cohomology J R q).Linear R := by
  unfold cohomology
  infer_instance

/-- Original constant abelian coefficients and original cohomology, before scalar enrichment. -/
abbrev constantCohomologyAb (q : ℕ) : ModuleCat.{max u v} R ⥤ AddCommGrpCat.{e} :=
  forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v} ⋙
    constantSheaf J AddCommGrpCat.{max u v} ⋙ CategoryTheory.Sheaf.functorH J q

/-- Constant coefficients with their original cohomology and canonical coefficient action. -/
def constantCohomology (q : ℕ) : ModuleCat.{max u v} R ⥤ ModuleCat.{e} R :=
  Functor.moduleValued R (constantCohomologyAb J R q)

instance constantCohomology_additive (q : ℕ) : (constantCohomology J R q).Additive :=
  inferInstanceAs (Functor.moduleValued R (constantCohomologyAb J R q)).Additive

instance constantCohomology_linear (q : ℕ) : (constantCohomology J R q).Linear R := by
  unfold constantCohomology
  infer_instance

/-- Constant coefficient maps retain the native constant-sheaf map and original `Sheaf.H.map`. -/
@[simp]
theorem constantCohomology_map_apply {M N : ModuleCat.{max u v} R}
    (f : M ⟶ N) (q : ℕ) (x : (constantCohomology J R q).obj M) :
    (constantCohomology J R q).map f x = CategoryTheory.Sheaf.H.map
      ((constantSheaf J AddCommGrpCat.{max u v}).map
        ((forget₂ (ModuleCat.{max u v} R) AddCommGrpCat.{max u v}).map f)) q x := rfl

end ModuleCat.Sheaf
