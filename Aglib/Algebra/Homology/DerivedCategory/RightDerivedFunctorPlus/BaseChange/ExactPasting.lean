/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.ExactSquare
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.SquarePasting
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.ComparisonSquares

/-! # Transport of original horizontal pasting through exact derived comparisons -/

@[expose] public noncomputable section

namespace CategoryTheory

open CategoryTheory.Functor

universe wA wB wC wD wE wF

variable {A B C D E F : Type*}
  [Category* A] [Abelian A] [HasDerivedCategory.{wA} A] [EnoughInjectives A]
  [Category* B] [Abelian B] [HasDerivedCategory.{wB} B] [EnoughInjectives B]
  [Category* C] [Abelian C] [HasDerivedCategory.{wC} C] [EnoughInjectives C]
  [Category* D] [Abelian D] [HasDerivedCategory.{wD} D] [EnoughInjectives D]
  [Category* E] [Abelian E] [HasDerivedCategory.{wE} E] [EnoughInjectives E]
  [Category* F] [Abelian F] [HasDerivedCategory.{wF} F]
  {L₀ : A ⥤ B} {L₁ : C ⥤ D} {L₂ : E ⥤ F}
  {G₁ : A ⥤ C} {G₂ : C ⥤ E} {H₁ : B ⥤ D} {H₂ : D ⥤ F}
  {G : A ⥤ E} {H : B ⥤ F}
  [L₀.Additive] [L₁.Additive] [L₂.Additive]
  [G₁.Additive] [G₂.Additive] [H₁.Additive] [H₂.Additive]
  [G.Additive] [H.Additive]
  [L₀.PreservesHomology] [L₁.PreservesHomology] [L₂.PreservesHomology]
  [G₁.PreservesHomology] [G₂.PreservesHomology]
  [H₁.PreservesHomology] [H₂.PreservesHomology]
  [G.PreservesHomology] [H.PreservesHomology]

/-- The actual supplied derived squares inherit original horizontal pasting.
Only exact comparison maps are cancelled; no direct-image exactness is assumed. -/
theorem rightDerivedFunctorPlus_exactHorizontalPasting
    (α₁ : TwoSquare G₁ L₀ L₁ H₁) (α₂ : TwoSquare G₂ L₁ L₂ H₂)
    (α : TwoSquare G L₀ L₂ H) (γ : G ≅ G₁ ⋙ G₂) (δ : H ≅ H₁ ⋙ H₂)
    (α₁D : TwoSquare G₁.rightDerivedFunctorPlus L₀.rightDerivedFunctorPlus
      L₁.rightDerivedFunctorPlus H₁.rightDerivedFunctorPlus)
    (α₂D : TwoSquare G₂.rightDerivedFunctorPlus L₁.rightDerivedFunctorPlus
      L₂.rightDerivedFunctorPlus H₂.rightDerivedFunctorPlus)
    (αD : TwoSquare G.rightDerivedFunctorPlus L₀.rightDerivedFunctorPlus
      L₂.rightDerivedFunctorPlus H.rightDerivedFunctorPlus)
    (hα₁ : ∀ Z, ExactComparisonSquareEquation L₀ H₁ G₁ L₁ α₁ α₁D Z)
    (hα₂ : ∀ Z, ExactComparisonSquareEquation L₁ H₂ G₂ L₂ α₂ α₂D Z)
    (hα : ∀ Z, ExactComparisonSquareEquation L₀ H G L₂ α αD Z)
    (h : ∀ X, HorizontalSquareEquation α₁ α₂ α γ.hom δ.hom X)
    (K : DerivedCategory.Plus A) :
    HorizontalSquareEquation α₁D α₂D αD
      (G.rightDerivedFunctorPlusIso γ ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesHomology G₁ G₂).hom
      (H.rightDerivedFunctorPlusIso δ ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesHomology H₁ H₂).hom K := by
  let γD := G.rightDerivedFunctorPlusIso γ ≪≫
    rightDerivedFunctorPlusCompIsoOfPreservesHomology G₁ G₂
  let δD := H.rightDerivedFunctorPlusIso δ ≪≫
    rightDerivedFunctorPlusCompIsoOfPreservesHomology H₁ H₂
  have hQ (Z : CochainComplex.Plus A) :
      L₂.rightDerivedFunctorPlus.map (γD.hom.app (DerivedCategory.Plus.Q.obj Z)) ≫
        α₂D.app (G₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj Z)) ≫
        H₂.rightDerivedFunctorPlus.map (α₁D.app (DerivedCategory.Plus.Q.obj Z)) =
      αD.app (DerivedCategory.Plus.Q.obj Z) ≫
        δD.hom.app (L₀.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj Z)) := by
    let t := H₂.rightDerivedFunctorPlus.map
        (H₁.rightDerivedFunctorPlus.map (L₀.rightDerivedFunctorPlusExactComparison.hom.app Z) ≫
          H₁.rightDerivedFunctorPlusExactComparison.hom.app (L₀.mapCochainComplexPlus.obj Z)) ≫
      H₂.rightDerivedFunctorPlusExactComparison.hom.app
        (H₁.mapCochainComplexPlus.obj (L₀.mapCochainComplexPlus.obj Z))
    have : IsIso t := by dsimp [t]; infer_instance
    have hc :
        L₂.mapCochainComplexPlus.map ((NatIso.mapCochainComplexPlus γ).hom.app Z) ≫
          α₂.mapCochainComplexPlus.app (G₁.mapCochainComplexPlus.obj Z) ≫
          H₂.mapCochainComplexPlus.map (α₁.mapCochainComplexPlus.app Z) =
        α.mapCochainComplexPlus.app Z ≫
          (NatIso.mapCochainComplexPlus δ).hom.app (L₀.mapCochainComplexPlus.obj Z) := by
      apply ObjectProperty.hom_ext
      ext n
      change L₂.map (γ.hom.app (Z.obj.X n)) ≫
          (𝟙 _ ≫ α₂.app (G₁.obj (Z.obj.X n)) ≫ 𝟙 _) ≫
          H₂.map (𝟙 _ ≫ α₁.app (Z.obj.X n) ≫ 𝟙 _) =
        (𝟙 _ ≫ α.app (Z.obj.X n) ≫ 𝟙 _) ≫ δ.hom.app (L₀.obj (Z.obj.X n))
      simpa only [HorizontalSquareEquation, Category.id_comp, Category.comp_id] using
        h (Z.obj.X n)
    have hγ := rightDerivedFunctorPlusCompIso_exactComparison_square G₁ G₂ G γ Z
    have hδ := rightDerivedFunctorPlusCompIso_exactComparison_square H₁ H₂ H δ
      (L₀.mapCochainComplexPlus.obj Z)
    simp only [Iso.trans_hom, NatTrans.comp_app, mapCochainComplexPlusCompIso,
      NatIso.ofComponents_hom_app, Iso.refl_hom, Category.comp_id] at hγ hδ
    change γD.hom.app (DerivedCategory.Plus.Q.obj Z) ≫
      (G₂.rightDerivedFunctorPlus.map (G₁.rightDerivedFunctorPlusExactComparison.hom.app Z) ≫
        G₂.rightDerivedFunctorPlusExactComparison.hom.app
          (G₁.mapCochainComplexPlus.obj Z)) = _ at hγ
    change δD.hom.app (DerivedCategory.Plus.Q.obj (L₀.mapCochainComplexPlus.obj Z)) ≫
      (H₂.rightDerivedFunctorPlus.map (H₁.rightDerivedFunctorPlusExactComparison.hom.app
        (L₀.mapCochainComplexPlus.obj Z)) ≫ H₂.rightDerivedFunctorPlusExactComparison.hom.app
          (H₁.mapCochainComplexPlus.obj (L₀.mapCochainComplexPlus.obj Z))) = _ at hδ
    have h₁ := hα₁ Z
    have h₂ := hα₂ (G₁.mapCochainComplexPlus.obj Z)
    have h₀ := hα Z
    simp only [ExactComparisonSquareEquation] at h₁ h₂ h₀
    have hn₂ := α₂D.naturality (G₁.rightDerivedFunctorPlusExactComparison.hom.app Z)
    have hnδ := δD.hom.naturality (L₀.rightDerivedFunctorPlusExactComparison.hom.app Z)
    have hnH := H₂.rightDerivedFunctorPlusExactComparison.hom.naturality
      (α₁.mapCochainComplexPlus.app Z)
    have hnL := L₂.rightDerivedFunctorPlusExactComparison.hom.naturality
      ((NatIso.mapCochainComplexPlus γ).hom.app Z)
    simp only [Functor.comp_obj, Functor.comp_map] at hn₂ hnδ hnH hnL
    let t₂ := H₂.rightDerivedFunctorPlus.map
        (L₁.rightDerivedFunctorPlus.map (G₁.rightDerivedFunctorPlusExactComparison.hom.app Z) ≫
          L₁.rightDerivedFunctorPlusExactComparison.hom.app (G₁.mapCochainComplexPlus.obj Z)) ≫
      H₂.rightDerivedFunctorPlusExactComparison.hom.app
        (L₁.mapCochainComplexPlus.obj (G₁.mapCochainComplexPlus.obj Z))
    let t₃ := L₂.rightDerivedFunctorPlus.map
        (G₂.rightDerivedFunctorPlus.map (G₁.rightDerivedFunctorPlusExactComparison.hom.app Z) ≫
          G₂.rightDerivedFunctorPlusExactComparison.hom.app (G₁.mapCochainComplexPlus.obj Z)) ≫
      L₂.rightDerivedFunctorPlusExactComparison.hom.app
        (G₂.mapCochainComplexPlus.obj (G₁.mapCochainComplexPlus.obj Z))
    let pG := L₂.rightDerivedFunctorPlus.map (G.rightDerivedFunctorPlusExactComparison.hom.app Z) ≫
      L₂.rightDerivedFunctorPlusExactComparison.hom.app (G.mapCochainComplexPlus.obj Z)
    let p₀ := H.rightDerivedFunctorPlus.map (L₀.rightDerivedFunctorPlusExactComparison.hom.app Z) ≫
      H.rightDerivedFunctorPlusExactComparison.hom.app (L₀.mapCochainComplexPlus.obj Z)
    have hpost : H₂.rightDerivedFunctorPlus.map
        (α₁D.app (DerivedCategory.Plus.Q.obj Z)) ≫ t =
        t₂ ≫ DerivedCategory.Plus.Q.map
          (H₂.mapCochainComplexPlus.map (α₁.mapCochainComplexPlus.app Z)) := by
      dsimp only [t, t₂]
      rw [← Category.assoc, ← Functor.map_comp, ← h₁]
      simp only [Functor.map_comp, Category.assoc]
      rw [hnH]
    have hpre : α₂D.app (G₁.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj Z)) ≫
        t₂ = t₃ ≫ DerivedCategory.Plus.Q.map
          (α₂.mapCochainComplexPlus.app (G₁.mapCochainComplexPlus.obj Z)) := by
      dsimp only [t₂, t₃]
      simp only [Functor.map_comp, Category.assoc]
      rw [← reassoc_of% hn₂, ← h₂]
    have hgamma : L₂.rightDerivedFunctorPlus.map
        (γD.hom.app (DerivedCategory.Plus.Q.obj Z)) ≫ t₃ =
        pG ≫ DerivedCategory.Plus.Q.map
          (L₂.mapCochainComplexPlus.map ((NatIso.mapCochainComplexPlus γ).hom.app Z)) := by
      dsimp only [t₃, pG]
      rw [← Category.assoc, ← Functor.map_comp]
      rw [hγ]
      simp only [Functor.map_comp, Category.assoc]
      exact congrArg (fun z => L₂.rightDerivedFunctorPlus.map
        (G.rightDerivedFunctorPlusExactComparison.hom.app Z) ≫ z) hnL
    have hdelta : δD.hom.app
        (L₀.rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj Z)) ≫ t =
        p₀ ≫ DerivedCategory.Plus.Q.map
          ((NatIso.mapCochainComplexPlus δ).hom.app (L₀.mapCochainComplexPlus.obj Z)) := by
      dsimp only [t, p₀]
      simp only [Functor.map_comp, Category.assoc]
      rw [← reassoc_of% hnδ, hδ]
    apply (cancel_mono t).mp
    simp only [Category.assoc]
    rw [hpost, reassoc_of% hpre, reassoc_of% hgamma, hdelta]
    change _ = αD.app (DerivedCategory.Plus.Q.obj Z) ≫ p₀ ≫ _
    rw [← Category.assoc (αD.app _) p₀, ← h₀]
    simp only [Category.assoc, ← Functor.map_comp]
    rw [hc]
    simp only [pG, Category.assoc]
  have he :
      whiskerRight γD.hom L₂.rightDerivedFunctorPlus ≫
          (TwoSquare.hComp α₁D α₂D).natTrans =
        αD.natTrans ≫ whiskerLeft L₀.rightDerivedFunctorPlus δD.hom := by
    apply Localization.natTrans_ext DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso A)
    intro Z
    simpa only [NatTrans.comp_app, whiskerRight_app, whiskerLeft_app,
      TwoSquare.hComp_app] using hQ Z
  simpa only [HorizontalSquareEquation, NatTrans.comp_app, whiskerRight_app,
    whiskerLeft_app, TwoSquare.hComp_app] using congr_app he K

end CategoryTheory
