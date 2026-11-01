/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.PastedRectangle

/-! # Whole normalized pasted-rectangle equations

The regular proposition retains the original source maps, both original routes
and the original target transport. Normalization is performed abstractly before
large concrete comparison maps are substituted.
-/

@[expose] public section

namespace CategoryTheory

/-- The normalized equation for two original routes through a pasted rectangle. -/
def PastedRectangleEquation {C : Type*} [Category C] {S A B T T' : C}
    (u : S ⟶ A) (v : S ⟶ B) (a : A ⟶ T) (b : B ⟶ T') (c : T' ⟶ T) : Prop :=
  u ≫ a = v ≫ b ≫ c

/-- Original route, transport and normalization equations give the unchanged
normalized rectangle with a shared regular proposition head. -/
theorem pastedRectangle_normalize_eq {C : Type*} [Category C]
    {S A B C₁ C₂ D E F G : C}
    (v₁ : S ⟶ A) (v₂ : S ⟶ B) (c₁ : A ≅ C₁) (c₂ : B ≅ C₂)
    (s₁ : A ⟶ D) (s₂ : B ⟶ E) (d₁ : D ≅ F) (d₂ : E ≅ G)
    (a : C₁ ⟶ F) (b : C₂ ⟶ G) (eS : A ≅ B) (eT : D ≅ E)
    (h₁ : c₁.hom ≫ a = s₁ ≫ d₁.hom)
    (h₂ : c₂.hom ≫ b = s₂ ≫ d₂.hom)
    (hS : v₁ ≫ eS.hom = v₂) (hT : s₁ ≫ eT.hom = eS.hom ≫ s₂)
    (u : S ⟶ C₁) (v : S ⟶ C₂) (c : G ⟶ F)
    (hu : v₁ ≫ c₁.hom = u) (hv : v₂ ≫ c₂.hom = v)
    (hc : d₂.inv ≫ eT.inv ≫ d₁.hom = c) :
    PastedRectangleEquation u v a b c := by
  unfold PastedRectangleEquation
  rw [← hu, ← hv, ← hc]
  simpa only [Category.assoc] using
    pastedRectangle_normalize v₁ v₂ c₁ c₂ s₁ s₂ d₁ d₂ a b eS eT h₁ h₂ hS hT

end CategoryTheory
