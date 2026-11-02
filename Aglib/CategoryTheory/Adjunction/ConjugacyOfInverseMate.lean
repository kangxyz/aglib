/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Original conjugacy determined by an inverse square and its two mates -/
@[expose] public noncomputable section
namespace CategoryTheory
variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}

/-- An original inverse-square mate determines the conjugacy of the forward square. -/
theorem conjugateEquiv_eq_inv_of_inverse_mate
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : F₁ ⊣ U₁) (d : F₂ ⊣ U₂)
    (e : L₁ ⋙ F₂ ≅ F₁ ⋙ L₂) (r : U₂ ⋙ R₁ ≅ R₂ ⋙ U₁)
    (θ : R₁ ⋙ F₁ ⟶ F₂ ⋙ R₂)
    (he : (mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv)).natTrans = θ)
    (hr : (mateEquiv d c (TwoSquare.mk _ _ _ _ θ)).natTrans = r.hom) :
    conjugateEquiv (c.comp b) (a.comp d) e.hom = r.inv := by
  have hs : mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv) =
      TwoSquare.mk _ _ _ _ θ := by
    ext X
    exact congrArg (fun t => t.app X) he
  have hi : conjugateIsoEquiv (a.comp d) (c.comp b) e.symm = r := by
    apply Iso.ext
    exact (iterated_mateEquiv_conjugateEquiv a b c d
      (TwoSquare.mk _ _ _ _ e.inv)).symm.trans (by rw [hs]; exact hr)
  exact congrArg Iso.inv hi
end CategoryTheory
