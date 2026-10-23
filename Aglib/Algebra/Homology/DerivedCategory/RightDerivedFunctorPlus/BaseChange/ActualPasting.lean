/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.SquarePasting
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.VerticalNormalization
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.IdentityNormalization

/-!
# Pasting equations for actual exchange maps

These equations transfer native mate coherence through explicit equalities of
exchange maps, without unfolding the actual exchange-map aliases.
-/

@[expose] public section
namespace CategoryTheory

section Horizontal
variable {A B C D E F : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
  {R₀ : B ⥤ A} {R₁ : D ⥤ C} {R₂ : F ⥤ E}
  {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
  {G : A ⥤ E} {H : B ⥤ F}

/-- The literal horizontal equation, keeping all actual exchange maps opaque. -/
def ActualHorizontalMateEquation
    (β₁ : R₀ ⋙ G₁ ⟶ H₁ ⋙ R₁) (β₂ : R₁ ⋙ G₂ ⟶ H₂ ⋙ R₂)
    (β : R₀ ⋙ G ⟶ H ⋙ R₂) (γ : G ⟶ G₁ ⋙ G₂) (δ : H ⟶ H₁ ⋙ H₂)
    (K : B) : Prop :=
  γ.app (R₀.obj K) ≫ G₂.map (β₁.app K) ≫ β₂.app (H₁.obj K) =
    β.app K ≫ R₂.map (δ.app K)

/-- Extract the literal equation without unfolding any actual exchange-map alias. -/
theorem actualHorizontalMateEquation_eq
    (β₁ : R₀ ⋙ G₁ ⟶ H₁ ⋙ R₁) (β₂ : R₁ ⋙ G₂ ⟶ H₂ ⋙ R₂)
    (β : R₀ ⋙ G ⟶ H ⋙ R₂) (γ : G ⟶ G₁ ⋙ G₂) (δ : H ⟶ H₁ ⋙ H₂)
    (K : B) (h : ActualHorizontalMateEquation β₁ β₂ β γ δ K) :
    γ.app (R₀.obj K) ≫ G₂.map (β₁.app K) ≫ β₂.app (H₁.obj K) =
      β.app K ≫ R₂.map (δ.app K) := h

/-- Substitute already proved actual-map aliases before any concrete specialization. -/
theorem actualHorizontalMateEquation_of_mates
    {L₀ : A ⥤ B} {L₁ : C ⥤ D} {L₂ : E ⥤ F}
    (adj₀ : L₀ ⊣ R₀) (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α₁ : TwoSquare G₁ L₀ L₁ H₁) (α₂ : TwoSquare G₂ L₁ L₂ H₂)
    (α : TwoSquare G L₀ L₂ H) (γ : G ⟶ G₁ ⋙ G₂) (δ : H ⟶ H₁ ⋙ H₂)
    (β₁ : R₀ ⋙ G₁ ⟶ H₁ ⋙ R₁) (β₂ : R₁ ⋙ G₂ ⟶ H₂ ⋙ R₂)
    (β : R₀ ⋙ G ⟶ H ⋙ R₂)
    (hβ₁ : β₁ = (mateEquiv adj₀ adj₁ α₁).natTrans)
    (hβ₂ : β₂ = (mateEquiv adj₁ adj₂ α₂).natTrans)
    (hβ : β = (mateEquiv adj₀ adj₂ α).natTrans)
    (K : B) (h : HorizontalMateEquation α₁ α₂ α γ δ adj₀ adj₁ adj₂ K) :
    ActualHorizontalMateEquation β₁ β₂ β γ δ K := by
  subst β₁
  subst β₂
  subst β
  exact h
end Horizontal

section Vertical
variable {A B C D E F : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
  {G : A ⥤ D} {H : B ⥤ E} {K : C ⥤ F}
  {R₁ : B ⥤ A} {R₂ : E ⥤ D} {R₃ : C ⥤ B} {R₄ : F ⥤ E}
  {R₀ : C ⥤ A} {R₀' : F ⥤ D}

/-- The literal vertical equation, keeping actual exchanges and comparisons opaque. -/
def ActualVerticalMateEquation
    (β₁ : R₁ ⋙ G ⟶ H ⋙ R₂) (β₂ : R₃ ⋙ H ⟶ K ⋙ R₄)
    (β : R₀ ⋙ G ⟶ K ⋙ R₀') (d₁ : R₀ ⟶ R₃ ⋙ R₁) (d₂ : R₀' ⟶ R₄ ⋙ R₂)
    (M : C) : Prop :=
  G.map (d₁.app M) ≫ β₁.app (R₃.obj M) ≫ R₂.map (β₂.app M) =
    β.app M ≫ d₂.app (K.obj M)

/-- Extract the vertical equation without reducing the actual maps or comparisons. -/
theorem actualVerticalMateEquation_eq
    (β₁ : R₁ ⋙ G ⟶ H ⋙ R₂) (β₂ : R₃ ⋙ H ⟶ K ⋙ R₄)
    (β : R₀ ⋙ G ⟶ K ⋙ R₀') (d₁ : R₀ ⟶ R₃ ⋙ R₁) (d₂ : R₀' ⟶ R₄ ⋙ R₂)
    (M : C) (h : ActualVerticalMateEquation β₁ β₂ β d₁ d₂ M) :
    G.map (d₁.app M) ≫ β₁.app (R₃.obj M) ≫ R₂.map (β₂.app M) =
      β.app M ≫ d₂.app (K.obj M) := h

/-- Native vertical mate coherence passes through named actual-map equalities. -/
theorem actualVerticalMateEquation_of_mates
    {L₁ : A ⥤ B} {L₂ : D ⥤ E} {L₃ : B ⥤ C} {L₄ : E ⥤ F}
    {L₀ : A ⥤ C} {L₀' : D ⥤ F}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄)
    (adj₀ : L₀ ⊣ R₀) (adj₀' : L₀' ⊣ R₀')
    (α₁ : TwoSquare G L₁ L₂ H) (α₂ : TwoSquare H L₃ L₄ K)
    (α : TwoSquare G L₀ L₀' K) (d₁ : R₀ ≅ R₃ ⋙ R₁) (d₂ : R₀' ≅ R₄ ⋙ R₂)
    (β₁ : R₁ ⋙ G ⟶ H ⋙ R₂) (β₂ : R₃ ⋙ H ⟶ K ⋙ R₄)
    (β : R₀ ⋙ G ⟶ K ⋙ R₀')
    (hβ₁ : β₁ = (mateEquiv adj₁ adj₂ α₁).natTrans)
    (hβ₂ : β₂ = (mateEquiv adj₃ adj₄ α₂).natTrans)
    (hβ : β = (mateEquiv adj₀ adj₀' α).natTrans)
    (M : C) (h : VerticalMateEquation α₁ α₂ α d₁ d₂
      adj₁ adj₂ adj₃ adj₄ adj₀ adj₀' M) :
    ActualVerticalMateEquation β₁ β₂ β d₁.hom d₂.hom M := by
  subst β₁
  subst β₂
  subst β
  exact h
end Vertical

section Identity
variable {C D : Type*} [Category* C] [Category* D]
  {L₁ R₁ : C ⥤ C} {L₂ R₂ : D ⥤ D} {G : C ⥤ D}

/-- Identity normalization with the actual exchange transformation left opaque. -/
def ActualIdentityMateEquation (β : R₁ ⋙ G ⟶ G ⋙ R₂)
    (d₁ : R₁ ⟶ 𝟭 C) (d₂ : R₂ ⟶ 𝟭 D) (X : C) : Prop :=
  G.map (d₁.app X) = β.app X ≫ d₂.app (G.obj X)

/-- Extract the literal actual-map identity equation. -/
theorem actualIdentityMateEquation_eq (β : R₁ ⋙ G ⟶ G ⋙ R₂)
    (d₁ : R₁ ⟶ 𝟭 C) (d₂ : R₂ ⟶ 𝟭 D) (X : C)
    (h : ActualIdentityMateEquation β d₁ d₂ X) :
    G.map (d₁.app X) = β.app X ≫ d₂.app (G.obj X) := h

/-- Substitute the named actual-mate equality only at the generic boundary. -/
theorem actualIdentityMateEquation_of_mate
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ G)
    (d₁ : R₁ ≅ 𝟭 C) (d₂ : R₂ ≅ 𝟭 D) (β : R₁ ⋙ G ⟶ G ⋙ R₂)
    (hβ : β = (mateEquiv adj₁ adj₂ α).natTrans) (X : C)
    (h : IdentityMateEquation α d₁ d₂ adj₁ adj₂ X) :
    ActualIdentityMateEquation β d₁.hom d₂.hom X := by
  subst β
  exact h
end Identity

end CategoryTheory
