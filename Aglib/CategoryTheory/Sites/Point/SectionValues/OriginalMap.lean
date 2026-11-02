/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.Point.SectionValues

/-! # Whole section equations at their original map heads

Evaluate the supplied whole equation before identifying its factors with the
original named maps. The same additive groups and section maps are retained.
-/

@[expose] public section

open CategoryTheory

universe v

namespace CategoryTheory.OriginalSectionValues

/-- Evaluate the original whole equation with the supplied literal value views. -/
theorem germHom_apply_of_values
    {P R : Type*} [AddCommGroup P] [AddCommGroup R]
    {A B C : AddCommGrpCat.{v}} (σ : A ⟶ B) {β : B ⟶ C}
    (source : P →+ A) (target : R →+ C) {r : P →+ R}
    (h : (σ ≫ β).hom.comp source = target.comp r)
    (E : P → C) (hE : ∀ x, E x = β (σ (source x)))
    (x : P) (y : C) (hy : target (r x) = y) : E x = y :=
  (hE x).trans ((germHom_apply σ β source target r h x).trans hy)

/-- Transport the whole original arrow before applying the section functor. -/
theorem mapped_germHom_apply_of_values
    {D : Type*} [Category* D] (Γ : D ⥤ AddCommGrpCat.{v})
    {B C : D} (a : B ⟶ C) {b : B ⟶ C} (ha : a = b)
    {P R : Type*} [AddCommGroup P] [AddCommGroup R]
    {A : AddCommGrpCat.{v}} (σ : A ⟶ Γ.obj B)
    (source : P →+ A) (target : R →+ Γ.obj C) {r : P →+ R}
    (h : (σ ≫ Γ.map b).hom.comp source = target.comp r)
    (E : P → Γ.obj C) (hE : ∀ x, E x = Γ.map a (σ (source x)))
    (x : P) (y : Γ.obj C) (hy : target (r x) = y) : E x = y := by
  subst a
  exact germHom_apply_of_values σ source target h E hE x y hy

end CategoryTheory.OriginalSectionValues
