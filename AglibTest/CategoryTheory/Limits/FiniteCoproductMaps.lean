/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.CategoryTheory.Limits.FiniteCoproductMaps

/-!
# Maps out of and between finite coproducts

The declarations below restate the induction principle for maps out of finite coproducts and its
comparison over `Option`, restate the pullback squares of `Sigma.map` in a finitary extensive
category (here types), and guard their axioms.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AglibTest.FiniteCoproductMaps

/-- The induction principle for maps out of finite coproducts. -/
theorem induction {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] {X : C}
    (P : ∀ ⦃Y : C⦄, (Y ⟶ X) → Prop)
    (iso : ∀ ⦃Y Y' : C⦄ (e : Y ≅ Y') (f : Y' ⟶ X), P f → P (e.hom ≫ f))
    (initial : ∀ ⦃Y : C⦄ (f : Y ⟶ X), IsInitial Y → P f)
    (coprod : ∀ ⦃Y₁ Y₂ : C⦄ (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X), P f₁ → P f₂ → P (coprod.desc f₁ f₂))
    {J : Type w} [Finite J] {Y : J → C} (f : ∀ j, Y j ⟶ X) (hf : ∀ j, P (f j)) :
    P (Sigma.desc f) :=
  Sigma.desc_induction P iso initial coprod f hf

/-- Under `sigmaOptionIso`, `Sigma.desc` over `Option α` is a binary `coprod.desc`. -/
theorem option {C : Type u} [Category.{v} C] [HasFiniteCoproducts C] {α : Type w} [Finite α]
    {Y : Option α → C} {X : C} (f : ∀ o, Y o ⟶ X) :
    (sigmaOptionIso Y).hom ≫ Sigma.desc f =
      coprod.desc (f none) (Sigma.desc fun a => f (some a)) :=
  sigmaOptionIso_hom_desc f

/-- In the finitary extensive category of types, the inclusion of a summand is the pullback of the
corresponding summand along `Sigma.map f`. -/
theorem pullback_types {J : Type u} [Finite J] {X Y : J → Type u} (f : ∀ j, X j ⟶ Y j) (j : J) :
    IsPullback (Sigma.ι X j) (f j) (Limits.Sigma.map f) (Sigma.ι Y j) :=
  FinitaryExtensive.isPullback_sigmaι_sigmaMap f j

/-- info: 'AglibTest.FiniteCoproductMaps.induction' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.FiniteCoproductMaps.induction

/-- info: 'AglibTest.FiniteCoproductMaps.option' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.FiniteCoproductMaps.option

/-- info: 'AglibTest.FiniteCoproductMaps.pullback_types' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms AglibTest.FiniteCoproductMaps.pullback_types

end AglibTest.FiniteCoproductMaps
