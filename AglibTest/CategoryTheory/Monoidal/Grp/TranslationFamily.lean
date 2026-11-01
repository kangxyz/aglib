/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Monoidal.Grp.TranslationFamily

/-! # Whole parameterized translation in arbitrary cartesian monoidal categories -/

@[expose] public section

open CategoryTheory MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

universe v u

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  (G : C) [GrpObj G] {T T' : C}

example (a : T' ⟶ T) (f : T ⟶ G) :
    (𝟙 G ⊗ₘ a) ≫ (GrpObj.translationFamily G f).hom =
      (GrpObj.translationFamily G (a ≫ f)).hom ≫ (𝟙 G ⊗ₘ a) :=
  GrpObj.translationFamily_naturality G a f

example (f g : T ⟶ G) :
    GrpObj.translationFamily G (f * g) =
      GrpObj.translationFamily G f ≪≫ GrpObj.translationFamily G g :=
  GrpObj.translationFamily_mul G f g

example (f : T ⟶ G) :
    (GrpObj.translationFamily G f).symm = GrpObj.translationFamily G f⁻¹ :=
  GrpObj.translationFamily_symm G f

/--
info: 'CategoryTheory.GrpObj.translationFamily_naturality' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CategoryTheory.GrpObj.translationFamily_naturality
