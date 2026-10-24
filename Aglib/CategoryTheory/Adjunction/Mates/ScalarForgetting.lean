/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Adjunction.UnderlyingMate
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.HorizontalCube
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.VerticalNormalization

/-! # Original mates under scalar-forgetting comparisons

Unit compatibility identifies the mate of a coefficient comparison. Right
composition coherence then gives left composition coherence, before any site
or scheme is substituted. No fullness assumption is used.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace CategoryTheory

open TwoSquare

section Unit

variable {C D C' D' : Type*} [Category* C] [Category* D]
  [Category* C'] [Category* D']
  {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
  {U : C ⥤ C'} {V : D ⥤ D'}

/-- A unit-compatible original left comparison has the specified original right mate. -/
theorem mateEquiv_inv_eq_of_unit
    (adj : L ⊣ R) (adj' : L' ⊣ R') (e : L ⋙ V ≅ U ⋙ L')
    (d : R ⋙ U ≅ V ⋙ R')
    (h : ∀ X, U.map (adj.unit.app X) ≫ d.hom.app (L.obj X) ≫
      R'.map (e.hom.app X) = adj'.unit.app (U.obj X)) :
    mateEquiv adj adj' (TwoSquare.mk _ _ _ _ e.inv) =
      TwoSquare.mk _ _ _ _ d.hom := by
  apply TwoSquare.ext
  intro X
  exact congrArg (fun t => t.app X)
    (mateEquiv_inv_natTrans_eq_of_unit adj adj' e d.hom h)

end Unit

section Composition

variable {A B C D E F : Type*}
  [Category* A] [Category* B] [Category* C] [Category* D] [Category* E] [Category* F]
  {G : A ⥤ D} {H : B ⥤ E} {K : C ⥤ F}
  {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : D ⥤ E} {R₂ : E ⥤ D}
  {L₃ : B ⥤ C} {R₃ : C ⥤ B} {L₄ : E ⥤ F} {R₄ : F ⥤ E}
  {L₀ : A ⥤ C} {R₀ : C ⥤ A} {L₀' : D ⥤ F} {R₀' : F ⥤ D}

/-- Coherence of the original right mates implies the literal left comparison square. -/
theorem verticalSquareEquation_of_mateEquation
    (α : TwoSquare G L₁ L₂ H) (β : TwoSquare H L₃ L₄ K)
    (γ : TwoSquare G L₀ L₀' K)
    (c₁ : L₀ ≅ L₁ ⋙ L₃) (c₂ : L₀' ≅ L₂ ⋙ L₄)
    (d₁ : R₀ ≅ R₃ ⋙ R₁) (d₂ : R₀' ≅ R₄ ⋙ R₂)
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (adj₃ : L₃ ⊣ R₃) (adj₄ : L₄ ⊣ R₄)
    (adj₀ : L₀ ⊣ R₀) (adj₀' : L₀' ⊣ R₀')
    (hc₁ : conjugateEquiv (adj₁.comp adj₃) adj₀ c₁.hom = d₁.inv)
    (hc₂ : conjugateEquiv (adj₂.comp adj₄) adj₀' c₂.hom = d₂.inv)
    (h : ∀ M, VerticalMateEquation α β γ d₁ d₂
      adj₁ adj₂ adj₃ adj₄ adj₀ adj₀' M) (X : A) :
    VerticalSquareEquation α β γ c₁ c₂ X := by
  have hs : (α ≫ᵥ β).whiskerRight c₂.hom = γ.whiskerLeft c₁.hom := by
    apply (mateEquiv (adj₁.comp adj₃) adj₀').injective
    rw [mateEquiv_conjugateEquiv_vcomp, conjugateEquiv_mateEquiv_vcomp, hc₁, hc₂]
    ext M
    simp only [TwoSquare.whiskerBottom_app, TwoSquare.whiskerTop_app]
    rw [mateEquiv_vComp_app]
    apply (cancel_epi (G.map (d₁.hom.app M))).mp
    have hm := h M
    change G.map (d₁.hom.app M) ≫
        (mateEquiv adj₁ adj₂ α).natTrans.app (R₃.obj M) ≫
        R₂.map ((mateEquiv adj₃ adj₄ β).natTrans.app M) =
      (mateEquiv adj₀ adj₀' γ).natTrans.app M ≫ d₂.hom.app (K.obj M) at hm
    calc
      G.map (d₁.hom.app M) ≫
          (((mateEquiv adj₁ adj₂ α).natTrans.app (R₃.obj M) ≫
            R₂.map ((mateEquiv adj₃ adj₄ β).natTrans.app M)) ≫ d₂.inv.app (K.obj M)) =
        (G.map (d₁.hom.app M) ≫
          (mateEquiv adj₁ adj₂ α).natTrans.app (R₃.obj M) ≫
            R₂.map ((mateEquiv adj₃ adj₄ β).natTrans.app M)) ≫ d₂.inv.app (K.obj M) := by
              simp only [Category.assoc]
      _ = (mateEquiv adj₀ adj₀' γ).natTrans.app M := by
        rw [hm, Category.assoc, d₂.hom_inv_id_app]
        exact Category.comp_id ((mateEquiv adj₀ adj₀' γ).natTrans.app M)
      _ = G.map (d₁.hom.app M) ≫
          (G.map (d₁.inv.app M) ≫ (mateEquiv adj₀ adj₀' γ).natTrans.app M) := by
        rw [← G.map_comp_assoc, d₁.hom_inv_id_app]
        exact ((congrArg
          (fun t => t ≫ (mateEquiv adj₀ adj₀' γ).natTrans.app M)
          (G.map_id (R₀.obj M))).trans
            (Category.id_comp ((mateEquiv adj₀ adj₀' γ).natTrans.app M))).symm
  simpa only [TwoSquare.whiskerRight_app, TwoSquare.whiskerLeft_app,
    TwoSquare.vComp_app, VerticalSquareEquation] using congrArg (fun s => s.app X) hs

end Composition

section SquareTransport

variable {C D : Type*} [Category* C] [Category* D] (U : C ⥤ D)
  {A₀ A₁ B₀ B₁ : C} {C₀ C₁ D₀ D₁ : D}

/-- Compatible composition comparisons transport the original three-factor square. -/
theorem comparison_square_of_comp
    (a : A₀ ≅ A₁) (b : B₀ ≅ B₁) (q : A₀ ≅ B₀)
    (a' : C₀ ≅ C₁) (b' : D₀ ≅ D₁) (q' : C₀ ≅ D₀)
    (s : C₁ ⟶ U.obj A₁) (t : D₁ ⟶ U.obj B₁)
    (v : C₀ ⟶ U.obj A₀) (w : D₀ ⟶ U.obj B₀)
    (ha : a'.hom ≫ s = v ≫ U.map a.hom)
    (hb : b'.hom ≫ t = w ≫ U.map b.hom)
    (hq : q'.hom ≫ w = v ≫ U.map q.hom) :
    s ≫ U.map (a.inv ≫ q.hom ≫ b.hom) =
      (a'.inv ≫ q'.hom ≫ b'.hom) ≫ t := by
  apply (cancel_epi a'.hom).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [← Category.assoc a'.hom s, ha]
  simp only [Category.assoc]
  rw [← U.map_comp_assoc, a.hom_inv_id, U.map_id, Category.id_comp]
  rw [← reassoc_of% hq, ← hb]
  simp only [← Category.assoc, a'.hom_inv_id, Category.id_comp]

/-- The hom form of an original comparison square follows from its inverse form. -/
theorem hom_square_of_inv {X X' Y Y' : C} (p : X ≅ X') (q : Y ≅ Y')
    (a : X ⟶ Y) (b : X' ⟶ Y') (h : b ≫ q.inv = p.inv ≫ a) :
    a ≫ q.hom = p.hom ≫ b := by
  apply (Iso.eq_comp_inv q).mp
  simpa only [Category.assoc] using ((Iso.eq_inv_comp p).mp h).symm

/-- Equality transport is natural in an arbitrary family of original arrows. -/
theorem arrow_family_eqToHom {I : Sort*} (F G : I → C) (a : ∀ i, F i ⟶ G i)
    {i j : I} (h : i = j) :
    eqToHom (congrArg F h) ≫ a j = a i ≫ eqToHom (congrArg G h) := by
  subst j
  simp

end SquareTransport

end CategoryTheory
