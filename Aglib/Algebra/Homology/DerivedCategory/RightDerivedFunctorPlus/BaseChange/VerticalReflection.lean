/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.VerticalNormalization

/-!
# Reflecting vertical coherence through actual mates

The native mates equivalence reflects coherence of the original left squares when the
right comparison isomorphisms are their actual conjugates. No square or mate is required
to be invertible. The scalar-forgetting inverse-image comparisons consume this reflection
to recover their original vertical coherence from direct-image comparison coherence.
-/

@[expose] public section

namespace CategoryTheory

section ConjugateComparisons

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {L₁ L₁' : A ⥤ B} {R₁ R₁' : B ⥤ A}
  {L₂ L₂' : C ⥤ D} {R₂ R₂' : D ⥤ C} {G : A ⥤ C} {H : B ⥤ D}

/-- Actual conjugate comparisons preserve and reflect commutativity of the original
left squares, without requiring the squares or their mates to be invertible. -/
theorem mateEquiv_conjugate_comparisons_iff
    (adj₁ : L₁ ⊣ R₁) (adj₁' : L₁' ⊣ R₁')
    (adj₂ : L₂ ⊣ R₂) (adj₂' : L₂' ⊣ R₂')
    (c₁ : L₁' ≅ L₁) (c₂ : L₂' ≅ L₂)
    (d₁ : R₁' ≅ R₁) (d₂ : R₂' ≅ R₂)
    (hc₁ : conjugateEquiv adj₁ adj₁' c₁.hom = d₁.inv)
    (hc₂ : conjugateEquiv adj₂ adj₂' c₂.hom = d₂.inv)
    (α : TwoSquare G L₁ L₂ H) (β : TwoSquare G L₁' L₂' H) :
    α.whiskerRight c₂.hom = β.whiskerLeft c₁.hom ↔
      ∀ M, G.map (d₁.hom.app M) ≫ (mateEquiv adj₁ adj₂ α).app M =
        (mateEquiv adj₁' adj₂' β).app M ≫ d₂.hom.app (H.obj M) := by
  constructor
  · intro h M
    exact mateEquiv_conjugate_comparisons adj₁ adj₁' adj₂ adj₂'
      c₁ c₂ d₁ d₂ hc₁ hc₂ α β h M
  · intro h
    apply (mateEquiv adj₁ adj₂').injective
    rw [mateEquiv_conjugateEquiv_vcomp, conjugateEquiv_mateEquiv_vcomp, hc₁, hc₂]
    ext M
    change (mateEquiv adj₁ adj₂ α).app M ≫ d₂.inv.app (H.obj M) =
      G.map (d₁.inv.app M) ≫ (mateEquiv adj₁' adj₂' β).app M
    apply (cancel_mono (d₂.hom.app (H.obj M))).mp
    simp only [Category.assoc, Iso.inv_hom_id_app]
    rw [← h M, ← Category.assoc, ← G.map_comp, Iso.inv_hom_id_app,
      G.map_id]
    exact (Category.comp_id ((mateEquiv adj₁ adj₂ α).natTrans.app M)).trans
      (Category.id_comp ((mateEquiv adj₁ adj₂ α).natTrans.app M)).symm

end ConjugateComparisons

section VerticalPasting

variable {A B C D E F : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
  {G : A ⥤ D} {H : B ⥤ E} {K : C ⥤ F}
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
  {L₃ : B ⥤ C} {R₃ : C ⥤ B} {L₄ : E ⥤ F} {R₄ : F ⥤ E}
  {L₀ : A ⥤ C} {R₀ : C ⥤ A} {L₀' : D ⥤ F} {R₀' : F ⥤ D}
  (α : TwoSquare G L₁ L₂ H) (β : TwoSquare H L₃ L₄ K)
  (γ : TwoSquare G L₀ L₀' K)
  (c₁ : L₀ ≅ L₁ ⋙ L₃) (c₂ : L₀' ≅ L₂ ⋙ L₄)
  (d₁ : R₀ ≅ R₃ ⋙ R₁) (d₂ : R₀' ≅ R₄ ⋙ R₂)

/-- Normalized vertical coherence of the actual mates reflects vertical coherence of
the original left squares under the actual conjugate comparisons. -/
theorem verticalSquareEquation
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄)
    (adj₀ : L₀ ⊣ R₀) (adj₀' : L₀' ⊣ R₀')
    (hc₁ : conjugateEquiv (adj₁.comp adj₃) adj₀ c₁.hom = d₁.inv)
    (hc₂ : conjugateEquiv (adj₂.comp adj₄) adj₀' c₂.hom = d₂.inv)
    (h : ∀ M, VerticalMateEquation α β γ d₁ d₂ adj₁ adj₂ adj₃ adj₄ adj₀ adj₀' M)
    (X : A) : VerticalSquareEquation α β γ c₁ c₂ X := by
  have hs : (TwoSquare.vComp α β).whiskerRight c₂.hom = γ.whiskerLeft c₁.hom := by
    apply (mateEquiv_conjugate_comparisons_iff (adj₁.comp adj₃) adj₀
      (adj₂.comp adj₄) adj₀' c₁ c₂ d₁ d₂ hc₁ hc₂ (TwoSquare.vComp α β) γ).mpr
    intro M
    rw [mateEquiv_vComp_app]
    exact h M
  simpa only [TwoSquare.whiskerRight_app, TwoSquare.whiskerLeft_app,
    TwoSquare.vComp_app, VerticalSquareEquation] using congr_app hs X

end VerticalPasting

end CategoryTheory
