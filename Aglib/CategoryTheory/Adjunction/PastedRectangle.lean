/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.EqToHom

/-! # Normalizing two pasted comparison routes

This categorical cancellation lemma retains both original route equations,
the equality-transport square and the specified source/target comparisons.
It does not supply a geometric pasting or refinement square.
-/

@[expose] public section

namespace CategoryTheory

/-- Two proved pasted routes and their original comparison square give the
normalized rectangle with the specified target comparison. -/
theorem pastedRectangle_normalize {C : Type*} [Category C]
    {S A B C₁ C₂ D E F G : C}
    (v₁ : S ⟶ A) (v₂ : S ⟶ B) (c₁ : A ≅ C₁) (c₂ : B ≅ C₂)
    (s₁ : A ⟶ D) (s₂ : B ⟶ E) (d₁ : D ≅ F) (d₂ : E ≅ G)
    (a : C₁ ⟶ F) (b : C₂ ⟶ G) (eS : A ≅ B) (eT : D ≅ E)
    (h₁ : c₁.hom ≫ a = s₁ ≫ d₁.hom)
    (h₂ : c₂.hom ≫ b = s₂ ≫ d₂.hom)
    (hS : v₁ ≫ eS.hom = v₂) (hT : s₁ ≫ eT.hom = eS.hom ≫ s₂) :
    v₁ ≫ c₁.hom ≫ a =
      v₂ ≫ c₂.hom ≫ b ≫ d₂.inv ≫ eT.inv ≫ d₁.hom := by
  rw [h₁, reassoc_of% h₂]
  simp only [Iso.hom_inv_id_assoc]
  rw [← hS, Category.assoc, ← reassoc_of% hT]
  simp

/-- Normalization of an original invertible compositor by its original right unit. -/
theorem iso_inv_comp_of_comp_eq {C : Type*} [Category C] {X Y Z : C}
    (a : X ≅ Y) (b : Y ≅ Z) (e : X ≅ Z) (h : a ≪≫ b = e) :
    e.symm ≪≫ a = b.symm := by
  rw [← h]
  simp

/-- Equality transports around a triangle agree at every original component. -/
theorem eqToIso_app_triangle {C D : Type*} [Category C] [Category D]
    {F G H : C ⥤ D} (e : F = H) (f : G = H) (g : F = G) (K : C) :
    (eqToIso e).inv.app K ≫ (eqToIso g).hom.app K = (eqToIso f).inv.app K := by
  subst G
  subst H
  simp

end CategoryTheory
