/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.SquareEqualityTransport
public import Aglib.CategoryTheory.Functor.CompositionCubeWhole

/-! # Retaining square equality transport behind the original whole predicate -/

@[expose] public section

namespace CategoryTheory.Functor

universe uA vA uB vB uC vC uD vD uI uJ

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {I : Type uI} {J : Type uJ} (L : I → A ⥤ B) (L' : J → C ⥤ D)
  (G : A ⥤ C) (H : B ⥤ D) (P : I → J → Prop)
  (e : ∀ i j, P i j → (G ⋙ L' j ≅ L i ⋙ H))

/-- The original whole comparison-transport predicate follows from equality
of the two indices, without evaluating a concrete square component. -/
theorem comparisonTransportEquation_of_squareFamily
    (i₀ i₁ : I) (j₀ j₁ : J) (h₀ : P i₀ j₀) (h₁ : P i₁ j₁)
    (a : i₀ = i₁) (b : j₀ = j₁) :
    ComparisonTransportEquation (e i₀ j₀ h₀).symm (e i₁ j₁ h₁).symm
      (eqToIso (congrArg L a)) (eqToIso (congrArg L' b)) :=
  squareIso_eqToIso_transport L L' G H P e i₀ i₁ j₀ j₁ h₀ h₁ a b

end CategoryTheory.Functor
