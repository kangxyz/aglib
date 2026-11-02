/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.OriginalUnitUniqueness
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.Adjunction.ComparisonSquares

/-!
# Deriving an original exchange isomorphism

The independently derived original right exchange agrees with the installed
mate when the original left square satisfies its exact comparison equation.
The proof uses the original derived units; no nonexact unit is cancelled.
-/

@[expose] public noncomputable section

open CategoryTheory.Functor

namespace CategoryTheory

universe uA vA wA uB vB wB uC vC wC uD vD wD

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  [EnoughInjectives A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  [EnoughInjectives B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]
  [EnoughInjectives C]
  {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{wD} D]
  [EnoughInjectives D]
  {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A}
  {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  [G.Additive] [H.Additive] [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
  [G.PreservesHomology] [H.PreservesHomology]
  [L₁.PreservesHomology] [L₂.PreservesHomology]
  [R₁.PreservesInjectiveObjects] [H.PreservesInjectiveObjects]
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
  (α : TwoSquare G L₁ L₂ H)
  (αD : TwoSquare G.rightDerivedFunctorPlus L₁.rightDerivedFunctorPlus
    L₂.rightDerivedFunctorPlus H.rightDerivedFunctorPlus)

/-- An independently derived original exchange isomorphism is the installed mate. -/
theorem derivedMate_eq_derivedIso
    (h : ∀ Z : CochainComplex.Plus A, ExactComparisonSquareEquation L₁ H G L₂ α αD Z)
    (e : R₁ ⋙ G ≅ H ⋙ R₂) (he : e.hom = (mateEquiv adj₁ adj₂ α).natTrans) :
    (mateEquiv adj₁.rightDerivedFunctorPlus adj₂.rightDerivedFunctorPlus αD).natTrans =
      ((rightDerivedFunctorPlusCompIsoOfPreservesInjectives R₁ G).symm ≪≫
        (R₁ ⋙ G).rightDerivedFunctorPlusIso e ≪≫
        rightDerivedFunctorPlusCompIsoOfPreservesInjectives H R₂).hom := by
  apply derivedMate_eq_of_originalUnit adj₁ adj₂ α αD h
  intro K
  have heK : (NatIso.mapCochainComplexPlus e).hom.app K =
      ((mateEquiv adj₁ adj₂ α).mapCochainComplexPlus).natTrans.app K := by
    apply ObjectProperty.hom_ext
    ext n
    change e.hom.app (K.obj.X n) =
      𝟙 _ ≫ (mateEquiv adj₁ adj₂ α).natTrans.app (K.obj.X n) ≫ 𝟙 _
    simpa only [Category.id_comp, Category.comp_id] using
      congrArg (fun t => t.app (K.obj.X n)) he
  rw [← heK]
  have hH := H.rightDerivedFunctorPlusExactComparison.inv_hom_id_app K
  have hG := G.rightDerivedFunctorPlusExactComparison.inv_hom_id_app
    (R₁.mapCochainComplexPlus.obj K)
  rw [rightDerivedFunctorPlusExactComparison_inv_app] at hH hG
  have hc₂ : (H ⋙ R₂).rightDerivedFunctorPlusUnit.app K ≫
      (rightDerivedFunctorPlusCompIsoOfPreservesInjectives H R₂).hom.app
        (DerivedCategory.Plus.Q.obj K) ≫
      R₂.rightDerivedFunctorPlus.map (H.rightDerivedFunctorPlusExactComparison.hom.app K) =
        R₂.rightDerivedFunctorPlusUnit.app (H.mapCochainComplexPlus.obj K) := by
    rw [← Category.assoc, rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom_app,
      Category.assoc, ← R₂.rightDerivedFunctorPlus.map_comp, hH]
    have hm := R₂.rightDerivedFunctorPlus.map_id
      ((H.mapCochainComplexPlus ⋙ DerivedCategory.Plus.Q).obj K)
    rw [hm]
    exact Category.comp_id _
  apply (cancel_epi (G.rightDerivedFunctorPlusExactComparison.inv.app
    (R₁.mapCochainComplexPlus.obj K))).mp
  rw [rightDerivedFunctorPlusExactComparison_inv_app]
  dsimp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]
  simp only [← Category.assoc]
  rw [← rightDerivedFunctorPlusCompIsoOfPreservesInjectives_hom_app R₁ G K]
  simp only [Category.assoc, Iso.hom_inv_id_app]
  have hc₁ : (R₁ ⋙ G).rightDerivedFunctorPlusUnit.app K ≫
      𝟙 ((R₁ ⋙ G).rightDerivedFunctorPlus.obj (DerivedCategory.Plus.Q.obj K)) =
        (R₁ ⋙ G).rightDerivedFunctorPlusUnit.app K := Category.comp_id _
  rw [← Category.assoc, hc₁]
  rw [← Category.assoc, rightDerivedFunctorPlusIso_hom_app]
  simp only [Category.assoc]
  rw [hc₂]
  rw [← Category.assoc, hG]
  exact (Category.id_comp _).symm

end CategoryTheory
