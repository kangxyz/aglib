/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactCube
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.ExactTriangleComposition
public import
  Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.SquarePasting

/-! # Original horizontal pasting on full derived categories -/

@[expose] public noncomputable section

namespace CategoryTheory

open CategoryTheory.Functor CategoryTheory.Limits

universe wA wB wC wD wE wF

variable {A B C D E F : Type*}
  [Category* A] [Abelian A] [HasDerivedCategory.{wA} A]
  [Category* B] [Abelian B] [HasDerivedCategory.{wB} B]
  [Category* C] [Abelian C] [HasDerivedCategory.{wC} C]
  [Category* D] [Abelian D] [HasDerivedCategory.{wD} D]
  [Category* E] [Abelian E] [HasDerivedCategory.{wE} E]
  [Category* F] [Abelian F] [HasDerivedCategory.{wF} F]
  {L₀ : A ⥤ B} {L₁ : C ⥤ D} {L₂ : E ⥤ F}
  {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
  {G : A ⥤ E} {H : B ⥤ F}
  [L₀.Additive] [L₁.Additive] [L₂.Additive]
  [G₁.Additive] [G₂.Additive] [H₁.Additive] [H₂.Additive]
  [G.Additive] [H.Additive]
  [PreservesFiniteLimits L₀] [PreservesFiniteColimits L₀] [PreservesFiniteLimits L₁]
    [PreservesFiniteColimits L₁] [PreservesFiniteLimits L₂] [PreservesFiniteColimits L₂]
  [PreservesFiniteLimits G₁] [PreservesFiniteColimits G₁] [PreservesFiniteLimits G₂]
    [PreservesFiniteColimits G₂]
  [PreservesFiniteLimits H₁] [PreservesFiniteColimits H₁] [PreservesFiniteLimits H₂]
    [PreservesFiniteColimits H₂]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] [PreservesFiniteLimits H]
    [PreservesFiniteColimits H]

/-- The actual supplied derived squares inherit original horizontal pasting.
Only original all-complex exact factors are cancelled; no direct-image exactness is assumed. -/
theorem mapDerivedCategory_exactHorizontalPasting
    (α₁ : TwoSquare G₁ L₀ L₁ H₁) (α₂ : TwoSquare G₂ L₁ L₂ H₂)
    (α : TwoSquare G L₀ L₂ H) (γ : G ≅ G₁ ⋙ G₂) (δ : H ≅ H₁ ⋙ H₂)
    (α₁D : TwoSquare G₁.mapDerivedCategory L₀.mapDerivedCategory
      L₁.mapDerivedCategory H₁.mapDerivedCategory)
    (α₂D : TwoSquare G₂.mapDerivedCategory L₁.mapDerivedCategory
      L₂.mapDerivedCategory H₂.mapDerivedCategory)
    (αD : TwoSquare G.mapDerivedCategory L₀.mapDerivedCategory
      L₂.mapDerivedCategory H.mapDerivedCategory)
    (hα₁ : ∀ Z, ExactFactorSquareEquation L₀ H₁ G₁ L₁ α₁ α₁D Z)
    (hα₂ : ∀ Z, ExactFactorSquareEquation L₁ H₂ G₂ L₂ α₂ α₂D Z)
    (hα : ∀ Z, ExactFactorSquareEquation L₀ H G L₂ α αD Z)
    (h : ∀ X, HorizontalSquareEquation α₁ α₂ α γ.hom δ.hom X)
    (K : DerivedCategory A) :
    HorizontalSquareEquation α₁D α₂D αD
      (mapDerivedCategoryCompositeIso G₁ G₂ G γ).hom
      (mapDerivedCategoryCompositeIso H₁ H₂ H δ).hom K := by
  let γD := mapDerivedCategoryCompositeIso G₁ G₂ G γ
  let δD := mapDerivedCategoryCompositeIso H₁ H₂ H δ
  have hQ (Z : CochainComplex A ℤ) :
      L₂.mapDerivedCategory.map (γD.hom.app (DerivedCategory.Q.obj Z)) ≫
        α₂D.app (G₁.mapDerivedCategory.obj (DerivedCategory.Q.obj Z)) ≫
        H₂.mapDerivedCategory.map (α₁D.app (DerivedCategory.Q.obj Z)) =
      αD.app (DerivedCategory.Q.obj Z) ≫
        δD.hom.app (L₀.mapDerivedCategory.obj (DerivedCategory.Q.obj Z)) := by
    let t := H₂.mapDerivedCategory.map
        (H₁.mapDerivedCategory.map (L₀.mapDerivedCategoryFactors.hom.app Z) ≫
          H₁.mapDerivedCategoryFactors.hom.app ((L₀.mapHomologicalComplex (.up ℤ)).obj Z)) ≫
      H₂.mapDerivedCategoryFactors.hom.app
        ((H₁.mapHomologicalComplex (.up ℤ)).obj ((L₀.mapHomologicalComplex (.up ℤ)).obj Z))
    have : IsIso t := by dsimp [t]; infer_instance
    have hc :
        (L₂.mapHomologicalComplex (.up ℤ)).map ((NatIso.mapHomologicalComplex γ (.up
          ℤ)).hom.app Z) ≫
          (α₂.natTrans.mapHomologicalComplex (.up ℤ)).app ((G₁.mapHomologicalComplex (.up
            ℤ)).obj Z) ≫
          (H₂.mapHomologicalComplex (.up ℤ)).map ((α₁.natTrans.mapHomologicalComplex (.up
            ℤ)).app Z) =
        (α.natTrans.mapHomologicalComplex (.up ℤ)).app Z ≫
          (NatIso.mapHomologicalComplex δ (.up ℤ)).hom.app ((L₀.mapHomologicalComplex (.up
            ℤ)).obj Z) := by
      ext n
      exact h (Z.X n)
    have hγ := mapDerivedCategoryCompositeIso_fac G₁ G₂ G γ Z
    have hδ := mapDerivedCategoryCompositeIso_fac H₁ H₂ H δ
      ((L₀.mapHomologicalComplex (.up ℤ)).obj Z)
    change γD.hom.app (DerivedCategory.Q.obj Z) ≫
      (G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app Z) ≫
        G₂.mapDerivedCategoryFactors.hom.app
          ((G₁.mapHomologicalComplex (.up ℤ)).obj Z)) = _ at hγ
    change δD.hom.app (DerivedCategory.Q.obj ((L₀.mapHomologicalComplex (.up ℤ)).obj Z)) ≫
      (H₂.mapDerivedCategory.map (H₁.mapDerivedCategoryFactors.hom.app
        ((L₀.mapHomologicalComplex (.up ℤ)).obj Z)) ≫ H₂.mapDerivedCategoryFactors.hom.app
          ((H₁.mapHomologicalComplex (.up ℤ)).obj
            ((L₀.mapHomologicalComplex (.up ℤ)).obj Z))) = _ at hδ
    have h₁ := hα₁ Z
    have h₂ := hα₂ ((G₁.mapHomologicalComplex (.up ℤ)).obj Z)
    have h₀ := hα Z
    simp only [ExactFactorSquareEquation] at h₁ h₂ h₀
    have hn₂ := α₂D.naturality (G₁.mapDerivedCategoryFactors.hom.app Z)
    have hnδ := δD.hom.naturality (L₀.mapDerivedCategoryFactors.hom.app Z)
    have hnH := H₂.mapDerivedCategoryFactors.hom.naturality
      ((α₁.natTrans.mapHomologicalComplex (.up ℤ)).app Z)
    have hnL := L₂.mapDerivedCategoryFactors.hom.naturality
      ((NatIso.mapHomologicalComplex γ (.up ℤ)).hom.app Z)
    simp only [Functor.comp_obj, Functor.comp_map] at hn₂ hnδ hnH hnL
    change H₂.mapDerivedCategory.map
        (DerivedCategory.Q.map ((α₁.natTrans.mapHomologicalComplex (.up ℤ)).app Z)) ≫
      H₂.mapDerivedCategoryFactors.hom.app
        ((H₁.mapHomologicalComplex (.up ℤ)).obj ((L₀.mapHomologicalComplex (.up ℤ)).obj Z)) =
      H₂.mapDerivedCategoryFactors.hom.app
        ((L₁.mapHomologicalComplex (.up ℤ)).obj ((G₁.mapHomologicalComplex (.up ℤ)).obj Z)) ≫
      DerivedCategory.Q.map ((H₂.mapHomologicalComplex (.up ℤ)).map
        ((α₁.natTrans.mapHomologicalComplex (.up ℤ)).app Z)) at hnH
    let t₂ := H₂.mapDerivedCategory.map
        (L₁.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app Z) ≫
          L₁.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj Z)) ≫
      H₂.mapDerivedCategoryFactors.hom.app
        ((L₁.mapHomologicalComplex (.up ℤ)).obj ((G₁.mapHomologicalComplex (.up ℤ)).obj Z))
    let t₃ := L₂.mapDerivedCategory.map
        (G₂.mapDerivedCategory.map (G₁.mapDerivedCategoryFactors.hom.app Z) ≫
          G₂.mapDerivedCategoryFactors.hom.app ((G₁.mapHomologicalComplex (.up ℤ)).obj Z)) ≫
      L₂.mapDerivedCategoryFactors.hom.app
        ((G₂.mapHomologicalComplex (.up ℤ)).obj ((G₁.mapHomologicalComplex (.up ℤ)).obj Z))
    let pG := L₂.mapDerivedCategory.map (G.mapDerivedCategoryFactors.hom.app Z) ≫
      L₂.mapDerivedCategoryFactors.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj Z)
    let p₀ := H.mapDerivedCategory.map (L₀.mapDerivedCategoryFactors.hom.app Z) ≫
      H.mapDerivedCategoryFactors.hom.app ((L₀.mapHomologicalComplex (.up ℤ)).obj Z)
    have hpost : H₂.mapDerivedCategory.map
        (α₁D.app (DerivedCategory.Q.obj Z)) ≫ t =
        t₂ ≫ DerivedCategory.Q.map
          ((H₂.mapHomologicalComplex (.up ℤ)).map ((α₁.natTrans.mapHomologicalComplex (.up
            ℤ)).app Z)) := by
      dsimp only [t, t₂]
      rw [← Category.assoc, ← Functor.map_comp, ← h₁]
      simp only [Functor.map_comp, Category.assoc]
      rw [hnH]
    have hpre : α₂D.app (G₁.mapDerivedCategory.obj (DerivedCategory.Q.obj Z)) ≫
        t₂ = t₃ ≫ DerivedCategory.Q.map
          ((α₂.natTrans.mapHomologicalComplex (.up ℤ)).app ((G₁.mapHomologicalComplex (.up
            ℤ)).obj Z)) := by
      dsimp only [t₂, t₃]
      simp only [Functor.map_comp, Category.assoc]
      rw [← reassoc_of% hn₂, ← h₂]
    have hgamma : L₂.mapDerivedCategory.map
        (γD.hom.app (DerivedCategory.Q.obj Z)) ≫ t₃ =
        pG ≫ DerivedCategory.Q.map
          ((L₂.mapHomologicalComplex (.up ℤ)).map ((NatIso.mapHomologicalComplex γ (.up
            ℤ)).hom.app Z)) := by
      dsimp only [t₃, pG]
      rw [← Category.assoc, ← Functor.map_comp]
      rw [hγ]
      simp only [Functor.map_comp, Category.assoc]
      exact congrArg (fun z => L₂.mapDerivedCategory.map
        (G.mapDerivedCategoryFactors.hom.app Z) ≫ z) hnL
    have hdelta : δD.hom.app
        (L₀.mapDerivedCategory.obj (DerivedCategory.Q.obj Z)) ≫ t =
        p₀ ≫ DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex δ (.up ℤ)).hom.app ((L₀.mapHomologicalComplex (.up
            ℤ)).obj Z)) := by
      dsimp only [t, p₀]
      simp only [Functor.map_comp, Category.assoc]
      rw [← reassoc_of% hnδ, hδ]
    apply (cancel_mono t).mp
    simp only [Category.assoc]
    rw [hpost, reassoc_of% hpre, reassoc_of% hgamma, hdelta]
    change _ = αD.app (DerivedCategory.Q.obj Z) ≫ p₀ ≫ _
    rw [← Category.assoc (αD.app _) p₀, ← h₀]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [hc]
    simp only [pG, Category.assoc]
  have he :
      whiskerRight γD.hom L₂.mapDerivedCategory ≫
          (TwoSquare.hComp α₁D α₂D).natTrans =
        αD.natTrans ≫ whiskerLeft L₀.mapDerivedCategory δD.hom := by
    apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso A (.up ℤ))
    intro Z
    simpa only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      TwoSquare.hComp_app] using hQ Z
  simpa only [HorizontalSquareEquation, NatTrans.comp_app, whiskerRight_app,
    whiskerLeft_app, TwoSquare.hComp_app] using congr_app he K

end CategoryTheory
