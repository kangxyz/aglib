/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Functor.CompositionChoice

/-! # Descent of an original composition square between independent models -/

@[expose] public section
namespace CategoryTheory
variable {A B C : Type*} [Category* A] [Category* B] [Category* C]
  {F₀ F₁ P₀ P₁ : A ⥤ B} {G₀ G₁ Q₀ Q₁ : B ⥤ C}
  {H₀ H₁ R₀ R₁ : A ⥤ C}

/-- Actual model comparison squares descend without identifying any model families. -/
theorem compositionFamilySquare
    (eF : F₀ ≅ F₁) (eG : G₀ ≅ G₁) (eH : H₀ ≅ H₁)
    (p₀ : F₀ ≅ P₀) (p₁ : F₁ ≅ P₁) (q₀ : G₀ ≅ Q₀) (q₁ : G₁ ≅ Q₁)
    (r₀ : H₀ ≅ R₀) (r₁ : H₁ ≅ R₁)
    (s : P₀ ≅ P₁) (t : Q₀ ≅ Q₁) (u : R₀ ≅ R₁)
    (κ₀ : F₀ ⋙ G₀ ≅ H₀) (κ₁ : F₁ ⋙ G₁ ≅ H₁)
    (α₀ : P₀ ⋙ Q₀ ≅ R₀) (α₁ : P₁ ⋙ Q₁ ≅ R₁)
    (hp : eF ≪≫ p₁ = p₀ ≪≫ s) (hq : eG ≪≫ q₁ = q₀ ≪≫ t)
    (hr : eH ≪≫ r₁ = r₀ ≪≫ u)
    (hk₀ : compositionPairIso p₀ q₀ ≪≫ α₀ = κ₀ ≪≫ r₀)
    (hk₁ : compositionPairIso p₁ q₁ ≪≫ α₁ = κ₁ ≪≫ r₁)
    (hα : compositionPairIso s t ≪≫ α₁ = α₀ ≪≫ u) :
    compositionPairIso eF eG ≪≫ κ₁ = κ₀ ≪≫ eH := by
  have h : (compositionPairIso eF eG ≪≫ κ₁) ≪≫ r₁ = (κ₀ ≪≫ eH) ≪≫ r₁ := by
    calc
      _ = compositionPairIso eF eG ≪≫ (compositionPairIso p₁ q₁ ≪≫ α₁) := by
        rw [Iso.trans_assoc, hk₁]
      _ = compositionPairIso p₀ q₀ ≪≫ (compositionPairIso s t ≪≫ α₁) := by
        rw [← Iso.trans_assoc, compositionPairIso_trans, hp, hq,
          ← compositionPairIso_trans, Iso.trans_assoc]
      _ = (κ₀ ≪≫ r₀) ≪≫ u := by rw [hα, ← Iso.trans_assoc, hk₀]
      _ = _ := by rw [Iso.trans_assoc, ← hr, ← Iso.trans_assoc]
  have h' := congrArg (fun z => z ≪≫ r₁.symm) h
  simpa only [Iso.trans_assoc, Iso.self_symm_id, Iso.trans_refl] using h'

end CategoryTheory
