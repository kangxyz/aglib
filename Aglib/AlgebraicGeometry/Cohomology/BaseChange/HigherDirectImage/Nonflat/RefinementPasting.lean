/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.CategoryTheory.Iso

/-! # Pasting the actual local-comparison refinement diagrams

The categorical calculation is performed on abstract typed arrows. Its native
application supplies the original pullback, higher-image and coefficient
isomorphisms as arguments, keeping their definitions out of the calculation.
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Nonflat

universe u v

/-- Four original coefficient squares paste to the coefficient square of their composite. -/
theorem localComparison_naturality
    {C : Type u} [Category.{v} C]
    {E E' A A' B B' D D' F F' : C}
    (a : E ⟶ A) (b : A ⟶ B) (c : B ⟶ D) (d : D ⟶ F)
    (a' : E' ⟶ A') (b' : A' ⟶ B') (c' : B' ⟶ D') (d' : D' ⟶ F')
    (s : E ⟶ E') (t : A ⟶ A') (u : B ⟶ B') (v : D ⟶ D') (w : F ⟶ F')
    (ha : s ≫ a' = a ≫ t) (hb : t ≫ b' = b ≫ u)
    (hc : u ≫ c' = c ≫ v) (hd : v ≫ d' = d ≫ w) :
    s ≫ a' ≫ b' ≫ c' ≫ d' = a ≫ b ≫ c ≫ d ≫ w := by
  rw [reassoc_of% ha, reassoc_of% hb, reassoc_of% hc, hd]

/-- The original source pullback square, its naturality, and the higher-image open pasting
equation combine without unfolding any of their native definitions. -/
theorem localSource_paste
    {C : Type u} [Category.{v} C]
    {E₀ E₁ A₁ B₁ D₁ D₂ A₀ A₀' B₀ : C}
    (s : E₀ ⟶ E₁) (a : E₁ ⟶ A₁) (b : A₁ ⟶ B₁) (r : B₁ ⟶ D₁)
    (j : A₁ ⟶ A₀) (d : A₀ ⟶ D₁) (h : D₁ ⟶ D₂)
    (l : A₀ ⟶ A₀') (b₀ : A₀' ⟶ B₀) (v : B₀ ⟶ D₂) (a₀ : E₀ ⟶ A₀')
    (ha : a₀ = s ≫ a ≫ j ≫ l) (hn : b ≫ r = j ≫ d)
    (hf : l ≫ b₀ ≫ v = d ≫ h) :
    s ≫ a ≫ b ≫ r ≫ h = a₀ ≫ b₀ ≫ v := by
  rw [ha]
  simp only [Category.assoc]
  rw [reassoc_of% hn, hf]

/-- Compatible source, middle and target refinement squares give the corresponding square
of the transported local arrows. -/
theorem localComparison_paste
    {C : Type u} [Category.{v} C]
    {E₀ E₁ F₀ F₁ A₁ B₁ C₁ A₀ B₀ C₀ D₁ D₂ C₂ : C}
    (s : E₀ ≅ E₁) (t : F₀ ≅ F₁)
    (a₁ : E₁ ⟶ A₁) (b₁ : A₁ ⟶ B₁) (k₁ : B₁ ⟶ C₁) (d₁ : F₁ ≅ C₁)
    (a₀ : E₀ ⟶ A₀) (b₀ : A₀ ⟶ B₀) (k₀ : B₀ ⟶ C₀) (d₀ : F₀ ≅ C₀)
    (r : B₁ ≅ D₁) (h : D₁ ⟶ D₂) (k : D₂ ⟶ C₂) (z : C₁ ≅ C₂)
    (v : B₀ ⟶ D₂) (w : C₀ ≅ C₂)
    (hk : k₁ = r.hom ≫ h ≫ k ≫ z.inv)
    (hsource : s.hom ≫ a₁ ≫ b₁ ≫ r.hom ≫ h = a₀ ≫ b₀ ≫ v)
    (hmiddle : v ≫ k = k₀ ≫ w.hom)
    (htarget : t.inv ≫ d₀.hom ≫ w.hom = d₁.hom ≫ z.hom) :
    s.hom ≫ a₁ ≫ b₁ ≫ k₁ ≫ d₁.inv =
      a₀ ≫ b₀ ≫ k₀ ≫ d₀.inv ≫ t.hom := by
  have hi : t.symm ≪≫ d₀ ≪≫ w = d₁ ≪≫ z := by
    apply Iso.ext
    simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc] using htarget
  have hv := congrArg Iso.inv hi
  simp only [Iso.trans_inv, Iso.symm_inv] at hv
  have hw := congrArg (fun q => w.hom ≫ q) hv
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at hw
  rw [hk]
  simp only [Category.assoc]
  rw [reassoc_of% hsource, reassoc_of% hmiddle, ← hw]

end AlgebraicGeometry.Scheme.Modules.Nonflat
