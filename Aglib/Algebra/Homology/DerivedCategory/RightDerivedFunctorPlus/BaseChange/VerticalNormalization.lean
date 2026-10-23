/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange

/-! # Normalizing mates under actual conjugate adjunction comparisons -/

@[expose] public section
namespace CategoryTheory

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  {L₁ L₁' : A ⥤ B} {R₁ R₁' : B ⥤ A}
  {L₂ L₂' : C ⥤ D} {R₂ R₂' : D ⥤ C} {G : A ⥤ C} {H : B ⥤ D}

/-- A commuting comparison of left squares gives the normalized actual right mates.
The right comparisons must be the actual conjugates, not arbitrary isomorphisms. -/
theorem mateEquiv_conjugate_comparisons
    (adj₁ : L₁ ⊣ R₁) (adj₁' : L₁' ⊣ R₁')
    (adj₂ : L₂ ⊣ R₂) (adj₂' : L₂' ⊣ R₂')
    (c₁ : L₁' ≅ L₁) (c₂ : L₂' ≅ L₂)
    (d₁ : R₁' ≅ R₁) (d₂ : R₂' ≅ R₂)
    (hc₁ : conjugateEquiv adj₁ adj₁' c₁.hom = d₁.inv)
    (hc₂ : conjugateEquiv adj₂ adj₂' c₂.hom = d₂.inv)
    (α : TwoSquare G L₁ L₂ H) (β : TwoSquare G L₁' L₂' H)
    (h : α.whiskerRight c₂.hom = β.whiskerLeft c₁.hom) (K : B) :
    G.map (d₁.hom.app K) ≫ (mateEquiv adj₁ adj₂ α).app K =
      (mateEquiv adj₁' adj₂' β).app K ≫ d₂.hom.app (H.obj K) := by
  have hm := congrArg (fun s => (mateEquiv adj₁ adj₂' s).app K) h
  rw [mateEquiv_conjugateEquiv_vcomp, conjugateEquiv_mateEquiv_vcomp,
    hc₁, hc₂] at hm
  change (mateEquiv adj₁ adj₂ α).app K ≫ d₂.inv.app (H.obj K) =
    G.map (d₁.inv.app K) ≫ (mateEquiv adj₁' adj₂' β).app K at hm
  apply (cancel_mono (d₂.inv.app (H.obj K))).mp
  rw [Category.assoc, hm, ← Category.assoc, ← G.map_comp,
    Iso.hom_inv_id_app, G.map_id, Category.id_comp,
    Category.assoc, Iso.hom_inv_id_app]
  exact (Category.comp_id ((mateEquiv adj₁' adj₂' β).natTrans.app K)).symm

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

/-- Literal vertical coherence of the actual left squares and their comparisons. -/
def VerticalSquareEquation (X : A) : Prop :=
  c₂.hom.app (G.obj X) ≫ L₄.map (α.app X) ≫ β.app (L₁.obj X) =
    γ.app X ≫ K.map (c₁.hom.app X)

/-- Literal normalized vertical pasting of the actual mates. -/
def VerticalMateEquation
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄)
    (adj₀ : L₀ ⊣ R₀) (adj₀' : L₀' ⊣ R₀') (M : C) : Prop :=
  G.map (d₁.hom.app M) ≫ (mateEquiv adj₁ adj₂ α).app (R₃.obj M) ≫
      R₂.map ((mateEquiv adj₃ adj₄ β).app M) =
    (mateEquiv adj₀ adj₀' γ).app M ≫ d₂.hom.app (K.obj M)

/-- Actual conjugacy and actual square coherence give normalized vertical mate pasting. -/
theorem verticalMateEquation
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄)
    (adj₀ : L₀ ⊣ R₀) (adj₀' : L₀' ⊣ R₀')
    (hc₁ : conjugateEquiv (adj₁.comp adj₃) adj₀ c₁.hom = d₁.inv)
    (hc₂ : conjugateEquiv (adj₂.comp adj₄) adj₀' c₂.hom = d₂.inv)
    (h : ∀ X, VerticalSquareEquation α β γ c₁ c₂ X) (M : C) :
    VerticalMateEquation α β γ d₁ d₂ adj₁ adj₂ adj₃ adj₄ adj₀ adj₀' M := by
  have hs : (TwoSquare.vComp α β).whiskerRight c₂.hom = γ.whiskerLeft c₁.hom := by
    ext X
    simpa only [TwoSquare.whiskerRight_app, TwoSquare.whiskerLeft_app,
      TwoSquare.vComp_app, VerticalSquareEquation] using h X
  have hm := mateEquiv_conjugate_comparisons (adj₁.comp adj₃) adj₀
    (adj₂.comp adj₄) adj₀' c₁ c₂ d₁ d₂ hc₁ hc₂ (TwoSquare.vComp α β) γ hs M
  rw [mateEquiv_vComp_app] at hm
  exact hm

end VerticalPasting

end CategoryTheory
