/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.Sites.SheafCohomology.OriginalSections.Pullback
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-! # Whole original section unit and composition

Actual constant adjunctions and source comparisons determine the whole section
unit and composition laws. The proofs use the original counit at the actual
section object, before evaluating elements or choosing any Ext realization.
-/

@[expose] public noncomputable section

open CategoryTheory.Limits

namespace CategoryTheory.Adjunction

universe uC vC uD vD uE vE uV vV

section Counit

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {V : Type uV} [Category.{vV} V]
  {K : V ⥤ C} {Γ : C ⥤ V} {L : C ⥤ D} {R : D ⥤ C}
  {K' : V ⥤ D} {Δ : D ⥤ V}
  (constantAdj : K ⊣ Γ) (imageAdj : L ⊣ R) (constantAdj' : K' ⊣ Δ)
  (e : R ⋙ Γ ≅ Δ) (c : K ⋙ L ≅ K')
  (hc : c = leftAdjointCompIso constantAdj imageAdj constantAdj' e)

include hc in
/-- The original counit represents the whole section pullback itself. -/
theorem unitSectionsNatTrans_counit (Y : C) :
    constantAdj'.homEquiv (Γ.obj Y) (L.obj Y)
        (c.inv.app (Γ.obj Y) ≫ L.map (constantAdj.counit.app Y)) =
      (unitSectionsNatTrans imageAdj Γ e).app Y := by
  have ha : constantAdj.homEquiv (Γ.obj Y) Y (constantAdj.counit.app Y) =
      𝟙 (Γ.obj Y) := by
    rw [homEquiv_unit]
    exact constantAdj.right_triangle_components Y
  have h := unitSectionMap_homEquiv constantAdj imageAdj constantAdj' e c hc
    (constantAdj.counit.app Y)
  exact h.trans ((congrArg (fun b => b ≫ (unitSectionsNatTrans imageAdj Γ e).app Y) ha).trans
    (Category.id_comp _))

end Counit

section Identity

variable {C : Type uC} [Category.{vC} C] {V : Type uV} [Category.{vV} V]
  {K : V ⥤ C} {Γ : C ⥤ V} {L R : C ⥤ C}
  (constantAdj : K ⊣ Γ) (imageAdj : L ⊣ R)
  (e : R ⋙ Γ ≅ Γ) (c : K ⋙ L ≅ K)
  (hc : c = leftAdjointCompIso constantAdj imageAdj constantAdj e)
  (i : L ≅ 𝟭 C) (hi : ∀ A, i.hom.app (K.obj A) = c.hom.app A)

include hc hi in
/-- Whole ordinary sections satisfy the original identity law, without Ext. -/
@[reassoc]
theorem unitSectionsNatTrans_id (Y : C) :
    (unitSectionsNatTrans imageAdj Γ e).app Y ≫ Γ.map (i.hom.app Y) = 𝟙 _ := by
  let A := Γ.obj Y
  let a : K.obj A ⟶ Y := constantAdj.counit.app Y
  have h := unitSectionsNatTrans_counit constantAdj imageAdj constantAdj e c hc Y
  have hs : (c.inv.app A ≫ L.map a) ≫ i.hom.app Y = a := by
    rw [Category.assoc, i.hom.naturality a, hi]
    simpa only [Functor.id_map] using c.inv_hom_id_app_assoc A a
  calc
    (unitSectionsNatTrans imageAdj Γ e).app Y ≫ Γ.map (i.hom.app Y) =
        constantAdj.homEquiv A Y ((c.inv.app A ≫ L.map a) ≫ i.hom.app Y) := by
      exact ((constantAdj.homEquiv_naturality_right
        (c.inv.app A ≫ L.map a) (i.hom.app Y)).trans
          (congrArg (fun b => b ≫ Γ.map (i.hom.app Y)) h)).symm
    _ = constantAdj.homEquiv A Y a := congrArg (constantAdj.homEquiv A Y) hs
    _ = 𝟙 A := by
      rw [homEquiv_unit]
      exact constantAdj.right_triangle_components Y

end Identity

section Composition

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {E : Type uE} [Category.{vE} E] {V : Type uV} [Category.{vV} V]
  {K₀ : V ⥤ C} {Γ₀ : C ⥤ V} {K₁ : V ⥤ D} {Γ₁ : D ⥤ V}
  {K₂ : V ⥤ E} {Γ₂ : E ⥤ V}
  {F : C ⥤ D} {R : D ⥤ C} {G : D ⥤ E} {S : E ⥤ D}
  {H : C ⥤ E} {T : E ⥤ C}
  (constantAdj₀ : K₀ ⊣ Γ₀) (constantAdj₁ : K₁ ⊣ Γ₁) (constantAdj₂ : K₂ ⊣ Γ₂)
  (imageAdj₁ : F ⊣ R) (imageAdj₂ : G ⊣ S) (imageAdj₀ : H ⊣ T)
  (e₁ : R ⋙ Γ₀ ≅ Γ₁) (e₂ : S ⋙ Γ₁ ≅ Γ₂) (e₀ : T ⋙ Γ₀ ≅ Γ₂)
  (c₁ : K₀ ⋙ F ≅ K₁) (c₂ : K₁ ⋙ G ≅ K₂) (c₀ : K₀ ⋙ H ≅ K₂)
  (hc₁ : c₁ = leftAdjointCompIso constantAdj₀ imageAdj₁ constantAdj₁ e₁)
  (hc₂ : c₂ = leftAdjointCompIso constantAdj₁ imageAdj₂ constantAdj₂ e₂)
  (hc₀ : c₀ = leftAdjointCompIso constantAdj₀ imageAdj₀ constantAdj₂ e₀)
  (i : H ≅ F ⋙ G)
  (hi : ∀ A, c₀.inv.app A ≫ i.hom.app (K₀.obj A) =
    c₂.inv.app A ≫ G.map (c₁.inv.app A))

include hc₁ hc₂ hc₀ hi in
/-- Whole ordinary section composition follows from the original inverse source equation. -/
@[reassoc]
theorem unitSectionsNatTrans_comp (Y : C) :
    (unitSectionsNatTrans imageAdj₀ Γ₀ e₀).app Y ≫ Γ₂.map (i.hom.app Y) =
      (unitSectionsNatTrans imageAdj₁ Γ₀ e₁).app Y ≫
        (unitSectionsNatTrans imageAdj₂ Γ₁ e₂).app (F.obj Y) := by
  let A := Γ₀.obj Y
  let a : K₀.obj A ⟶ Y := constantAdj₀.counit.app Y
  have h₁ := unitSectionsNatTrans_counit constantAdj₀ imageAdj₁ constantAdj₁ e₁ c₁ hc₁ Y
  have h₀ := unitSectionsNatTrans_counit constantAdj₀ imageAdj₀ constantAdj₂ e₀ c₀ hc₀ Y
  have h₂ := unitSectionMap_homEquiv constantAdj₁ imageAdj₂ constantAdj₂ e₂ c₂ hc₂
    (c₁.inv.app A ≫ F.map a)
  have hs : (c₀.inv.app A ≫ H.map a) ≫ i.hom.app Y =
      c₂.inv.app A ≫ G.map (c₁.inv.app A ≫ F.map a) := by
    calc
      _ = c₀.inv.app A ≫ i.hom.app (K₀.obj A) ≫ G.map (F.map a) := by
        simpa only [Category.assoc, Functor.comp_map] using
          congrArg (fun q => c₀.inv.app A ≫ q) (i.hom.naturality a)
      _ = (c₂.inv.app A ≫ G.map (c₁.inv.app A)) ≫ G.map (F.map a) := by
        simpa only [Category.assoc] using
          congrArg (fun q => q ≫ G.map (F.map a)) (hi A)
      _ = _ := by simp only [Functor.map_comp, Category.assoc]
  calc
    (unitSectionsNatTrans imageAdj₀ Γ₀ e₀).app Y ≫ Γ₂.map (i.hom.app Y) =
        constantAdj₂.homEquiv A _ ((c₀.inv.app A ≫ H.map a) ≫ i.hom.app Y) := by
      exact ((constantAdj₂.homEquiv_naturality_right
        (c₀.inv.app A ≫ H.map a) (i.hom.app Y)).trans
          (congrArg (fun b => b ≫ Γ₂.map (i.hom.app Y)) h₀)).symm
    _ = constantAdj₂.homEquiv A _ (c₂.inv.app A ≫ G.map (c₁.inv.app A ≫ F.map a)) :=
      congrArg (constantAdj₂.homEquiv A _) hs
    _ = constantAdj₁.homEquiv A _ (c₁.inv.app A ≫ F.map a) ≫
        (unitSectionsNatTrans imageAdj₂ Γ₁ e₂).app (F.obj Y) := h₂
    _ = (unitSectionsNatTrans imageAdj₁ Γ₀ e₁).app Y ≫
        (unitSectionsNatTrans imageAdj₂ Γ₁ e₂).app (F.obj Y) :=
      congrArg (fun b => b ≫ (unitSectionsNatTrans imageAdj₂ Γ₁ e₂).app (F.obj Y)) h₁

end Composition

end CategoryTheory.Adjunction

namespace CategoryTheory.Functor.NaturalityTransport

/-- Pure isomorphism algebra for the original section-square factors. -/
theorem sectionSquareEvaluation_of_unit {C : Type*} [Category* C]
    {A B D E H J : C} (e : A ≅ B) (e' : H ≅ J)
    (v : D ⟶ E) (u : B ⟶ D) (d : A ⟶ E) (k : E ⟶ H)
    (φ : D ⟶ J) (z : B ⟶ J) (m : A ⟶ H)
    (hu : u ≫ v = e.inv ≫ d) (hm : m = d ≫ k)
    (hn : φ ≫ e'.inv = v ≫ k) (hz : z = u ≫ φ) :
    m ≫ e'.hom = e.hom ≫ z := by
  have hs : e.inv ≫ m = z ≫ e'.inv := by
    calc
      _ = e.inv ≫ (d ≫ k) := congrArg (fun q => e.inv ≫ q) hm
      _ = (e.inv ≫ d) ≫ k := (Category.assoc _ _ _).symm
      _ = (u ≫ v) ≫ k := congrArg (fun q => q ≫ k) hu.symm
      _ = u ≫ (φ ≫ e'.inv) :=
        (Category.assoc _ _ _).trans (congrArg (fun q => u ≫ q) hn.symm)
      _ = (u ≫ φ) ≫ e'.inv := (Category.assoc _ _ _).symm
      _ = _ := congrArg (fun q => q ≫ e'.inv) hz.symm
  exact e'.eq_comp_inv.mp
    ((e.inv_comp_eq.mp hs).trans (Category.assoc e.hom z e'.inv).symm)

end CategoryTheory.Functor.NaturalityTransport
