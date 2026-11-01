/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.CompositionChoice

/-! # A whole-map boundary for naturality of specified composition isomorphisms -/

@[expose] public section

namespace CategoryTheory

variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  {F₀ F₁ : A ⥤ B} {G₀ G₁ : B ⥤ C} {H₀ H₁ : A ⥤ C}

/-- The actual component-free map equation yields naturality of the specified isos. -/
theorem compositionIsoNaturality_of_originalMaps
    (s : F₀ ≅ F₁) (t : G₀ ≅ G₁) (u : H₀ ≅ H₁)
    (a₀ : F₀ ⋙ G₀ ≅ H₀) (a₁ : F₁ ⋙ G₁ ≅ H₁)
    (σ : F₀ ⟶ F₁) (τ : G₀ ⟶ G₁) (υ : H₀ ⟶ H₁)
    (hs : s.hom = σ) (ht : t.hom = τ) (hu : u.hom = υ)
    (h : Functor.whiskerRight σ G₀ ≫ Functor.whiskerLeft F₁ τ ≫ a₁.hom = a₀.hom ≫ υ) :
    compositionPairIso s t ≪≫ a₁ = a₀ ≪≫ u := by
  apply Iso.ext
  simpa only [compositionPairIso, Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, hs, ht, hu, Category.assoc] using h

end CategoryTheory
