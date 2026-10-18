/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Mathlib.CategoryTheory.FintypeCat

/-!
# NaturalityTransport

General constructions and comparisons for this native mathematical family.
-/

@[expose] public section

open CategoryTheory
namespace CategoryTheory.Functor.NaturalityTransport
universe u v

theorem functor_square_apply {C : Type v} [Category.{u} C] (F : C ⥤ FintypeCat.{u})
    {A A' B B' : C} (i : A ⟶ A') (j : B ⟶ B') (f : A ⟶ B) (g : A' ⟶ B')
    (h : i ≫ g = f ≫ j) (x : F.obj A) :
    F.map j (F.map f x) = F.map g (F.map i x) := by
  have he := congrArg F.map h
  rw [Functor.map_comp, Functor.map_comp] at he
  exact (ConcreteCategory.congr_hom he x).symm

theorem naturality_via_injective {A A' B B' : Type u}
    (i : A → A') (j : B → B') (hj : Function.Injective j) (f : A → B) (g : A' → B')
    (a : A → A) (a' : A' → A') (b : B → B) (b' : B' → B')
    (hsq : ∀ x, j (f x) = g (i x)) (hi : ∀ x, i (a x) = a' (i x))
    (hja : ∀ y, j (b y) = b' (j y)) (hg : ∀ x, g (a' x) = b' (g x)) (x : A) :
    f (a x) = b (f x) := by
  apply hj
  calc
    j (f (a x)) = g (i (a x)) := hsq _
    _ = g (a' (i x)) := congrArg g (hi x)
    _ = b' (g (i x)) := hg _
    _ = b' (j (f x)) := congrArg b' (hsq x).symm
    _ = j (b (f x)) := (hja _).symm

end CategoryTheory.Functor.NaturalityTransport

/- Migration source: the R5Lab/Aglib mirror; exact module in the migration record.
R5 revision c82abf3a72ce1e1cedf4a4f1fe08bea994ad4df5.
SHA256 467dcb06deb3bfa1a3fed825c29e664ac0ee442b5ff11681cfae7082b9f3ac1f.
Definitions, hypotheses and universes are retained modulo native names. -/
