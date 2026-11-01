/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.CompositionChoice

/-! # Attach original image-model squares to the chosen compositor -/

@[expose] public section
namespace CategoryTheory
variable {A B C : Type*} [Category* A] [Category* B] [Category* C]

/-- Refining only the first source comparison retains the original horizontal pair map. -/
theorem compositionPairIso_first
    {F F₀ F₁ : A ⥤ B} {G G₀ : B ⥤ C}
    (p₀ : F ≅ F₀) (p₁ : F ≅ F₁) (q : G ≅ G₀) (r : F₀ ≅ F₁)
    (hr : p₀ ≪≫ r = p₁) :
    compositionPairIso p₀ q ≪≫ Functor.isoWhiskerRight r G₀ = compositionPairIso p₁ q := by
  have h := compositionPairIso_trans p₀ r q (Iso.refl G₀)
  simpa only [compositionPairIso, Functor.isoWhiskerLeft_refl,
    Iso.trans_refl, hr] using h

variable {D : Type*} [Category* D] {U V S₀ S₁ T₀ T₁ : D}

/-- The original chosen map and actual raw map form this literal square. -/
def ChosenImageSquareEquation (s : U ⟶ S₁) (α : S₁ ⟶ T₁)
    (κ : U ⟶ V) (t : V ⟶ T₁) : Prop := s ≫ α = κ ≫ t

/-- Paste the proved original chosen, source, target and raw-map squares. -/
theorem chosenImageSquareEquation
    (s₀ : U ⟶ S₀) (s₁ : U ⟶ S₁) (t₀ : V ⟶ T₀) (t₁ : V ⟶ T₁)
    (κ : U ⟶ V) (α₀ : S₀ ⟶ T₀) (α₁ : S₁ ⟶ T₁)
    (r : S₀ ⟶ S₁) (q : T₀ ⟶ T₁)
    (hκ : s₀ ≫ α₀ = κ ≫ t₀) (hs : s₀ ≫ r = s₁)
    (ht : t₀ ≫ q = t₁) (hα : r ≫ α₁ = α₀ ≫ q) :
    ChosenImageSquareEquation s₁ α₁ κ t₁ := by
  rw [ChosenImageSquareEquation, ← hs, Category.assoc, hα,
    ← Category.assoc, hκ, Category.assoc, ht]

end CategoryTheory
