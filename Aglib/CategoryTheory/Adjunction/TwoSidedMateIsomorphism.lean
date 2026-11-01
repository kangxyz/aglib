/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Invertibility from the original mate on the opposite side -/

@[expose] public noncomputable section

namespace CategoryTheory

universe uA vA uB vB uC vC uD vD uI uJ

variable {A : Type uA} [Category.{vA} A] {B : Type uB} [Category.{vB} B]
  {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {F₁ : A ⥤ C} {U₁ : C ⥤ A} {F₂ : B ⥤ D} {U₂ : D ⥤ B}
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}

/-- A specified square is the mate of the inverse original left comparison
when the corresponding original right comparison is its horizontal mate. -/
theorem mateEquiv_inv_eq_of_conjugate
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : F₁ ⊣ U₁) (d : F₂ ⊣ U₂)
    (e : L₁ ⋙ F₂ ≅ F₁ ⋙ L₂) (r : U₂ ⋙ R₁ ≅ R₂ ⋙ U₁)
    (θ : R₁ ⋙ F₁ ⟶ F₂ ⋙ R₂)
    (he : conjugateEquiv (c.comp b) (a.comp d) e.hom = r.inv)
    (hr : (mateEquiv d c (TwoSquare.mk _ _ _ _ θ)).natTrans = r.hom) :
    (mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv)).natTrans = θ := by
  have hi : conjugateEquiv (a.comp d) (c.comp b) e.inv = r.hom := by
    have h : conjugateIsoEquiv (c.comp b) (a.comp d) e = r.symm := Iso.ext he
    exact congrArg Iso.inv h
  have h : mateEquiv d c (mateEquiv a b (TwoSquare.mk _ _ _ _ e.inv)) =
      mateEquiv d c (TwoSquare.mk _ _ _ _ θ) := by
    apply TwoSquare.ext
    intro X
    exact congrArg (fun t => t.app X)
      ((iterated_mateEquiv_conjugateEquiv a b c d
        (TwoSquare.mk _ _ _ _ e.inv)).trans (hi.trans hr.symm))
  exact congrArg TwoSquare.natTrans ((mateEquiv d c).injective h)

/-- Invertibility of the opposite original mate implies invertibility of the
actual horizontal mate, by the native iterated-mate/conjugate equation. -/
theorem isIso_mateEquiv_of_opposite_mate
    (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (c : F₁ ⊣ U₁) (d : F₂ ⊣ U₂)
    (e : F₁ ⋙ L₂ ≅ L₁ ⋙ F₂) (θ : R₁ ⋙ F₁ ⟶ F₂ ⋙ R₂)
    (h : (mateEquiv a b (TwoSquare.mk _ _ _ _ e.hom)).natTrans = θ) :
    IsIso ((mateEquiv d c (TwoSquare.mk _ _ _ _ θ)).natTrans) := by
  have he : (mateEquiv d c (TwoSquare.mk _ _ _ _ θ)).natTrans =
      conjugateEquiv (a.comp d) (c.comp b) e.hom := by
    have hs : mateEquiv a b (TwoSquare.mk _ _ _ _ e.hom) =
        TwoSquare.mk _ _ _ _ θ := by
      ext X
      exact congrArg (fun t => t.app X) h
    rw [← hs]
    exact iterated_mateEquiv_conjugateEquiv a b c d _
  rw [he]
  infer_instance

end CategoryTheory
