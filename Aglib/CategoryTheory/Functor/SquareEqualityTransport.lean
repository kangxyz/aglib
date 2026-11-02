/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.NatIso
public import Mathlib.CategoryTheory.EqToHom

/-! # Equality transport of a specified family of original squares

Keep the entire original square as a parameter before evaluating components.
This is equality transport, not an assumed coherence or invertibility theorem.
-/

@[expose] public section

namespace CategoryTheory.Functor

universe uA vA uB vB uC vC uD vD uI uJ

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {I : Type uI} {J : Type uJ} (L : I → A ⥤ B) (L' : J → C ⥤ D)
  (G : A ⥤ C) (H : B ⥤ D) (P : I → J → Prop)
  (e : ∀ i j, P i j → (G ⋙ L' j ≅ L i ⋙ H))

/-- Original square families commute with equality transport in both indices. -/
theorem squareIso_eqToIso_transport
    (i₀ i₁ : I) (j₀ j₁ : J) (h₀ : P i₀ j₀) (h₁ : P i₁ j₁)
    (a : i₀ = i₁) (b : j₀ = j₁) (X : A) :
    (eqToIso (congrArg L' b)).hom.app (G.obj X) ≫ (e i₁ j₁ h₁).hom.app X =
      (e i₀ j₀ h₀).hom.app X ≫ H.map ((eqToIso (congrArg L a)).hom.app X) := by
  subst i₁
  subst j₁
  simp

end CategoryTheory.Functor
