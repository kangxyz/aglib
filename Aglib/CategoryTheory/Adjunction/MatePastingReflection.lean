/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.VerticalNormalization

/-! # Reflecting actual pasting through adjunction mates

The converse of normalized vertical mate pasting retains the actual conjugate
compositors. It follows from injectivity of the original mate equivalence, not
from invertibility of arbitrary comparison maps between objects.
-/

@[expose] public section

universe uA vA uB vB uC vC uD vD
universe uE vE uF vF

namespace CategoryTheory

variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD} {E : Type uE}
  {F : Type uF}
  [Category.{vA} A] [Category.{vB} B] [Category.{vC} C] [Category.{vD} D] [Category.{vE} E]
    [Category.{vF} F]
  {G : A ⥤ D} {H : B ⥤ E} {K : C ⥤ F}
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
  {L₃ : B ⥤ C} {R₃ : C ⥤ B} {L₄ : E ⥤ F} {R₄ : F ⥤ E}
  {L₀ : A ⥤ C} {R₀ : C ⥤ A} {L₀' : D ⥤ F} {R₀' : F ⥤ D}

/-- Original normalized mate pasting reflects the original square pasting. -/
theorem verticalSquareEquation_of_mates
    (α : TwoSquare G L₁ L₂ H) (β : TwoSquare H L₃ L₄ K)
    (γ : TwoSquare G L₀ L₀' K)
    (c₁ : L₀ ≅ L₁ ⋙ L₃) (c₂ : L₀' ≅ L₂ ⋙ L₄)
    (d₁ : R₀ ≅ R₃ ⋙ R₁) (d₂ : R₀' ≅ R₄ ⋙ R₂)
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (a₃ : L₃ ⊣ R₃) (a₄ : L₄ ⊣ R₄)
    (a₀ : L₀ ⊣ R₀) (a₀' : L₀' ⊣ R₀')
    (hc₁ : conjugateEquiv (a₁.comp a₃) a₀ c₁.hom = d₁.inv)
    (hc₂ : conjugateEquiv (a₂.comp a₄) a₀' c₂.hom = d₂.inv)
    (h : ∀ M, VerticalMateEquation α β γ d₁ d₂ a₁ a₂ a₃ a₄ a₀ a₀' M)
    (X : A) : VerticalSquareEquation α β γ c₁ c₂ X := by
  have hs : (TwoSquare.vComp α β).whiskerRight c₂.hom = γ.whiskerLeft c₁.hom := by
    apply (mateEquiv (a₁.comp a₃) a₀').injective
    rw [mateEquiv_conjugateEquiv_vcomp, conjugateEquiv_mateEquiv_vcomp, hc₁, hc₂]
    ext M
    change (mateEquiv (a₁.comp a₃) (a₂.comp a₄) (TwoSquare.vComp α β)).app M ≫
        d₂.inv.app (K.obj M) =
      G.map (d₁.inv.app M) ≫ (mateEquiv a₀ a₀' γ).app M
    have hm : G.map (d₁.hom.app M) ≫
        (mateEquiv (a₁.comp a₃) (a₂.comp a₄) (TwoSquare.vComp α β)).app M =
        (mateEquiv a₀ a₀' γ).app M ≫ d₂.hom.app (K.obj M) := by
      simpa only [VerticalMateEquation, mateEquiv_vComp_app, Category.assoc] using h M
    apply (cancel_epi (G.map (d₁.hom.app M))).mp
    rw [← Category.assoc, hm]
    simp only [Category.assoc, Iso.hom_inv_id_app]
    rw [← G.map_comp_assoc, d₁.hom_inv_id_app, G.map_id, Category.id_comp]
    exact Category.comp_id _
  simpa only [VerticalSquareEquation, TwoSquare.whiskerRight_app,
    TwoSquare.whiskerLeft_app, TwoSquare.vComp_app] using congrArg (fun s => s.app X) hs

end CategoryTheory
