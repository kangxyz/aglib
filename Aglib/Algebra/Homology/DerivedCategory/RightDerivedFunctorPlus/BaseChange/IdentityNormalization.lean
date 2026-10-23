/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.VerticalNormalization

/-! # Identity exchange under the actual adjunction identity comparisons -/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D]
  {L₁ R₁ : C ⥤ C} {L₂ R₂ : D ⥤ D} {G : C ⥤ D}
  (α : TwoSquare G L₁ L₂ G) (c₁ : L₁ ≅ 𝟭 C) (c₂ : L₂ ≅ 𝟭 D)
  (d₁ : R₁ ≅ 𝟭 C) (d₂ : R₂ ≅ 𝟭 D)

/-- Literal normalization of the left square by its actual identity comparisons. -/
def IdentitySquareEquation (X : C) : Prop :=
  c₂.hom.app (G.obj X) = α.app X ≫ G.map (c₁.hom.app X)

/-- Literal normalization of the actual mate by the direct-image identity comparisons. -/
def IdentityMateEquation (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (X : C) : Prop :=
  G.map (d₁.hom.app X) = (mateEquiv adj₁ adj₂ α).app X ≫ d₂.hom.app (G.obj X)

/-- Identity normalization uses actual adjunction conjugacy, not arbitrary functor isos. -/
theorem identityMateEquation (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (hc₁ : conjugateEquiv Adjunction.id adj₁ c₁.hom = d₁.inv)
    (hc₂ : conjugateEquiv Adjunction.id adj₂ c₂.hom = d₂.inv)
    (h : ∀ X, IdentitySquareEquation α c₁ c₂ X) (X : C) :
    IdentityMateEquation α d₁ d₂ adj₁ adj₂ X := by
  have hs : (TwoSquare.vId G).whiskerRight c₂.hom = α.whiskerLeft c₁.hom := by
    ext Y
    simp only [TwoSquare.whiskerRight_app, TwoSquare.whiskerLeft_app, TwoSquare.vId_app]
    change c₂.hom.app (G.obj Y) ≫ 𝟙 (G.obj Y) = α.app Y ≫ G.map (c₁.hom.app Y)
    exact (CategoryTheory.Category.comp_id (c₂.hom.app (G.obj Y))).trans (h Y)
  have hm := mateEquiv_conjugate_comparisons Adjunction.id adj₁ Adjunction.id adj₂
    c₁ c₂ d₁ d₂ hc₁ hc₂ (TwoSquare.vId G) α hs X
  simp only [mateEquiv_vId, TwoSquare.hId_app] at hm
  change G.map (d₁.hom.app X) ≫ 𝟙 (G.obj X) =
    (mateEquiv adj₁ adj₂ α).app X ≫ d₂.hom.app (G.obj X) at hm
  exact (CategoryTheory.Category.comp_id (G.map (d₁.hom.app X))).symm.trans hm

end CategoryTheory
