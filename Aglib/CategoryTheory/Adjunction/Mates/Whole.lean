/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# Component normalization of the canonical base-change mate

The map is Mathlib's original `mateEquiv`, not a second exchange construction.
The equations here expose its component formula, uniqueness, identity normalization
and the two pasting formulas used by bounded-below derived direct images.
The adjunctions are parameters: this file does not construct derived adjunctions
or assert that an exchange map is invertible.
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

namespace CategoryTheory

open Category CategoryTheory.Functor TwoSquare

section Components

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {G : C ⥤ E} {H : D ⥤ F}
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- The canonical exchange component is the target unit, the square, and the source counit. -/
@[reassoc]
theorem mateEquiv_app_eq (α : TwoSquare G L₁ L₂ H) (K : D) :
    (mateEquiv adj₁ adj₂ α).app K =
      adj₂.unit.app (G.obj (R₁.obj K)) ≫
        R₂.map (α.app (R₁.obj K)) ≫ R₂.map (H.map (adj₁.counit.app K)) := by
  simp only [mateEquiv, Equiv.coe_fn_mk, NatTrans.comp_app,
    rightUnitor_inv_app, CategoryTheory.Functor.whiskerLeft_app, associator_hom_app,
    associator_inv_app, CategoryTheory.Functor.whiskerRight_app, leftUnitor_hom_app,
    comp_obj, CategoryTheory.Functor.comp_map, Category.id_comp]
  change adj₂.unit.app (G.obj (R₁.obj K)) ≫
      (R₂.map (α.app (R₁.obj K)) ≫
        (R₂.map (H.map (adj₁.counit.app K)) ≫ 𝟙 _)) = _
  rw [Category.comp_id]

/-- The counit equation determines the exchange transformation uniquely. -/
theorem eq_mateEquiv_iff (α : TwoSquare G L₁ L₂ H) (β : R₁ ⋙ G ⟶ H ⋙ R₂) :
    β = (mateEquiv adj₁ adj₂ α).natTrans ↔
      ∀ K : D, L₂.map (β.app K) ≫ adj₂.counit.app (H.obj K) =
        α.app (R₁.obj K) ≫ H.map (adj₁.counit.app K) := by
  constructor
  · rintro rfl K
    exact mateEquiv_counit adj₁ adj₂ α K
  · intro h
    ext K
    apply (adj₂.homEquiv _ _).symm.injective
    simp only [Adjunction.homEquiv_counit]
    exact (h K).trans (mateEquiv_counit adj₁ adj₂ α K).symm

end Components

section Identity

variable {C : Type u₁} {D : Type u₂}
  [Category.{v₁} C] [Category.{v₂} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)

-- These public identities are explicit rewrite rules.
-- Mathlib's mate formula owns the simp normal form.
/-- Identity base change has the vertical identity square as its canonical mate. -/
theorem mateEquiv_hId : mateEquiv adj adj (TwoSquare.hId L) = TwoSquare.vId R := by
  ext K
  rw [mateEquiv_app_eq]
  simp [TwoSquare.hId, TwoSquare.vId, adj.right_triangle_components]

/-- Identity vertical morphisms have the horizontal identity square as their mate. -/
theorem mateEquiv_vId (G : C ⥤ D) :
    mateEquiv Adjunction.id Adjunction.id (TwoSquare.vId G) = TwoSquare.hId G := by
  ext K
  rw [mateEquiv_app_eq]
  simp [TwoSquare.hId, TwoSquare.vId, Adjunction.id]

end Identity

section HorizontalBaseChange

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  {E : Type u₅} {F : Type u₆}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  [Category.{v₅} E] [Category.{v₆} F]
  {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  {L₃ : E ⥤ F} {R₃ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃)

/-- For successive base changes, first pull back the first exchange, then use the second.
The original `TwoSquare` composition retains all associators. -/
@[reassoc]
theorem mateEquiv_hComp_app (α : TwoSquare G₁ L₁ L₂ H₁)
    (β : TwoSquare G₂ L₂ L₃ H₂) (K : B) :
    (mateEquiv adj₁ adj₃ (α ≫ₕ β)).app K =
      G₂.map ((mateEquiv adj₁ adj₂ α).app K) ≫
        (mateEquiv adj₂ adj₃ β).app (H₁.obj K) := by
  rw [mateEquiv_vcomp adj₁ adj₂ adj₃]
  simp [TwoSquare.vComp]

end HorizontalBaseChange

section VerticalBaseChange

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄}
  {E : Type u₅} {F : Type u₆}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D]
  [Category.{v₅} E] [Category.{v₆} F]
  {G : A ⥤ D} {H : B ⥤ E} {K : C ⥤ F}
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
  {L₃ : B ⥤ C} {R₃ : C ⥤ B} {L₄ : E ⥤ F} {R₄ : F ⥤ E}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄)

/-- For composed vertical morphisms, use the first exchange at the inner direct image,
then apply the outer direct image to the second exchange. -/
@[reassoc]
theorem mateEquiv_vComp_app (α : TwoSquare G L₁ L₂ H)
    (β : TwoSquare H L₃ L₄ K) (M : C) :
    (mateEquiv (adj₁.comp adj₃) (adj₂.comp adj₄) (α ≫ᵥ β)).app M =
      (mateEquiv adj₁ adj₂ α).app (R₃.obj M) ≫
        R₂.map ((mateEquiv adj₃ adj₄ β).app M) := by
  rw [mateEquiv_hcomp adj₁ adj₂ adj₃ adj₄]
  simp [TwoSquare.hComp]

end VerticalBaseChange

end CategoryTheory

/-!
## Native comparison maps and normalized mate pasting

These categorical formulas use the original adjunctions and proved comparison
squares. They do not construct derived functors or assert exchange invertibility.
Whole comparison diagrams are kept in the separate Mates.Coherence module.
-/

section OriginalMateNaturality

namespace CategoryTheory

variable {C D E F : Type*} [Category* C] [Category* D] [Category* E] [Category* F]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  {G G' : C ⥤ E} {H H' : D ⥤ F}

/-- Naturality of native mates with respect to the top and bottom functors. -/
theorem mateEquiv_top_bottom_naturality (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (α : TwoSquare G L₁ L₂ H) (α' : TwoSquare G' L₁ L₂ H')
    (γ : G ⟶ G') (δ : H ⟶ H')
    (h : ∀ X, L₂.map (γ.app X) ≫ α'.app X = α.app X ≫ δ.app (L₁.obj X))
    (K : D) :
    γ.app (R₁.obj K) ≫ (mateEquiv adj₁ adj₂ α').app K =
      (mateEquiv adj₁ adj₂ α).app K ≫ R₂.map (δ.app K) := by
  apply (adj₂.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hn := adj₂.counit.naturality (δ.app K)
  change L₂.map (R₂.map (δ.app K)) ≫ adj₂.counit.app (H'.obj K) =
    adj₂.counit.app (H.obj K) ≫ δ.app K at hn
  rw [hn, reassoc_of% (mateEquiv_counit adj₁ adj₂ α K),
    mateEquiv_counit adj₁ adj₂ α' K]
  rw [← Category.assoc, h, Category.assoc, ← δ.naturality]
  rfl

end CategoryTheory

end OriginalMateNaturality

section OriginalHorizontalMatePasting

namespace CategoryTheory

variable {A B C D E F : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
  {L₀ : A ⥤ B} {R₀ : B ⥤ A} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
  {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
  {G : A ⥤ E} {H : B ⥤ F}
  (α₁ : TwoSquare G₁ L₀ L₁ H₁) (α₂ : TwoSquare G₂ L₁ L₂ H₂)
  (α : TwoSquare G L₀ L₂ H) (γ : G ⟶ G₁ ⋙ G₂) (δ : H ⟶ H₁ ⋙ H₂)

/-- Literal horizontal square coherence with its chosen comparison maps. -/
def HorizontalSquareEquation (X : A) : Prop :=
  L₂.map (γ.app X) ≫ α₂.app (G₁.obj X) ≫ H₂.map (α₁.app X) =
    α.app X ≫ δ.app (L₀.obj X)

/-- Literal horizontal exchange coherence under the actual three adjunctions. -/
def HorizontalMateEquation (adj₀ : L₀ ⊣ R₀) (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (K : B) : Prop :=
  γ.app (R₀.obj K) ≫ G₂.map ((mateEquiv adj₀ adj₁ α₁).app K) ≫
      (mateEquiv adj₁ adj₂ α₂).app (H₁.obj K) =
    (mateEquiv adj₀ adj₂ α).app K ≫ R₂.map (δ.app K)

/-- Native mate pasting transfers an actual square-coherence witness. -/
theorem horizontalMateEquation (adj₀ : L₀ ⊣ R₀) (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (h : ∀ X, HorizontalSquareEquation α₁ α₂ α γ δ X) (K : B) :
    HorizontalMateEquation α₁ α₂ α γ δ adj₀ adj₁ adj₂ K := by
  have hα : ∀ X, L₂.map (γ.app X) ≫ (TwoSquare.hComp α₁ α₂).app X =
      α.app X ≫ δ.app (L₀.obj X) := by
    intro X
    simpa only [HorizontalSquareEquation, TwoSquare.hComp_app] using h X
  have hm := mateEquiv_top_bottom_naturality adj₀ adj₂ α
    (TwoSquare.hComp α₁ α₂) γ δ hα K
  rw [mateEquiv_hComp_app adj₀ adj₁ adj₂] at hm
  exact hm

end CategoryTheory

end OriginalHorizontalMatePasting

section OriginalVerticalMateNormalization

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

end OriginalVerticalMateNormalization

section OriginalIdentityMateNormalization

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

end OriginalIdentityMateNormalization

section OriginalActualMatePasting

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

end OriginalActualMatePasting
