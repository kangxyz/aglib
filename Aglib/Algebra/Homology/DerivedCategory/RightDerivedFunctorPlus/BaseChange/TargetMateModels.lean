/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.BaseChange.TargetModels

/-! # Canonical native target transport of the original derived adjunction mate -/

@[expose] public noncomputable section
open CategoryTheory.Functor DerivedCategory.Plus
namespace CategoryTheory
universe uA vA uB vB uC vC uD vD dA dB dC₀ dC₁ dD
variable {A : Type uA} {B : Type uB} {C : Type uC} {D : Type uD}
  [Category.{vA} A] [Category.{vB} B] [Category.{vC} C] [Category.{vD} D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C] [EnoughInjectives D]
  (hA : HasDerivedCategory.{dA} A) (hB : HasDerivedCategory.{dB} B)
  (hC₀ : HasDerivedCategory.{dC₀} C) (hC₁ : HasDerivedCategory.{dC₁} C)
  (hD : HasDerivedCategory.{dD} D)
  {G : A ⥤ C} {H : B ⥤ D} {L₁ : A ⥤ B} {R₁ : B ⥤ A}
  {L₂ : C ⥤ D} {R₂ : D ⥤ C}
  [G.Additive] [H.Additive] [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive]
  [G.PreservesHomology] [H.PreservesHomology]
  [L₁.PreservesHomology] [L₂.PreservesHomology]
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ H)

/-- The actual native derived mate with every model specified independently. -/
abbrev rightDerivedMateModel
    (αD : TwoSquare ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hC₀ G _ _))
      ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hB L₁ _ _))
        ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hC₀ hD L₂ _ _))
      ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hB hD H _ _))) :
    (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hB hA R₁ _ _) ⋙
      (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hC₀ G _ _) ⟶
      (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hB hD H _ _) ⋙
        (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hD hC₀ R₂ _ _) := by
  letI := hA
  letI := hB
  letI := hC₀
  letI := hD
  exact (mateEquiv adj₁.rightDerivedFunctorPlus adj₂.rightDerivedFunctorPlus αD).natTrans

/-- The original mate-unit equation with explicitly retained native models. -/
def DerivedMateUnitEquationModel
    (αD : TwoSquare ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hC₀ G _ _))
      ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hB L₁ _ _))
        ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hC₀ hD L₂ _ _))
      ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hB hD H _ _))) (K : CochainComplex.Plus B) :
        Prop := by
  letI := hA
  letI := hB
  letI := hC₀
  letI := hD
  exact DerivedMateUnitEquation adj₁ adj₂ α αD K

/-- Remove only the literal identity complex-composition factors from the original unit equation. -/
theorem derivedMateUnitEquationModel_toTarget
    (αD : TwoSquare ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hC₀ G _ _))
      ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hB L₁ _ _))
        ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hC₀ hD L₂ _ _))
      ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hB hD H _ _))) (K : CochainComplex.Plus B)
    (hu : DerivedMateUnitEquationModel hA hB hC₀ hD adj₁ adj₂ α αD K) :
    DerivedTargetMateUnitEquation hA hB hC₀ hD G H R₁ R₂
      (mateEquiv adj₁ adj₂ α).natTrans (rightDerivedMateModel hA hB hC₀ hD adj₁ adj₂ αD) K := by
  let := hA
  let := hB
  let := hC₀
  let := hD
  have he : ((mateEquiv adj₁ adj₂ α).mapCochainComplexPlus).app K =
      ((mateEquiv adj₁ adj₂ α).natTrans.mapCochainComplexPlus).app K := by
    apply ObjectProperty.hom_ext
    ext n
    change (𝟙 _ ≫ (mateEquiv adj₁ adj₂ α).app (K.obj.X n) ≫ 𝟙 _) = _
    simp only [Category.id_comp, Category.comp_id]
    rfl
  change DerivedMateUnitEquation adj₁ adj₂ α αD K at hu
  rw [DerivedMateUnitEquation, he] at hu
  exact hu

/-- Original derived mates, not replacement maps, commute with canonical target-model transport. -/
theorem rightDerivedMateModel_target
    (αD₀ : TwoSquare ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hC₀ G _ _))
      ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hB L₁ _ _))
        ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hC₀ hD L₂ _ _))
      ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hB hD H _ _)))
    (αD₁ : TwoSquare ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hC₁ G _ _))
      ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hA hB L₁ _ _))
        ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hC₁ hD L₂ _ _))
      ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hB hD H _ _)))
    (hu₀ : ∀ K, DerivedMateUnitEquationModel hA hB hC₀ hD adj₁ adj₂ α αD₀ K)
    (hu₁ : ∀ K, DerivedMateUnitEquationModel hA hB hC₁ hD adj₁ adj₂ α αD₁ K) :
    whiskerRight (rightDerivedMateModel hA hB hC₀ hD adj₁ adj₂ αD₀)
        (canonicalEquivalence hC₀ hC₁).functor ≫
        (associator _ _ _).hom ≫
        whiskerLeft ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hB hD H _ _))
          (rightDerivedFunctorPlusChangeTarget hD hC₀ hC₁ R₂).hom =
      (associator _ _ _).hom ≫
        whiskerLeft ((@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hB hA R₁ _ _))
          (rightDerivedFunctorPlusChangeTarget hA hC₀ hC₁ G).hom ≫
        rightDerivedMateModel hA hB hC₁ hD adj₁ adj₂ αD₁ :=
  derivedTargetMate_square hA hB hC₀ hC₁ hD G H R₁ R₂ (mateEquiv adj₁ adj₂ α).natTrans
    (rightDerivedMateModel hA hB hC₀ hD adj₁ adj₂ αD₀)
    (rightDerivedMateModel hA hB hC₁ hD adj₁ adj₂ αD₁)
    (fun K => derivedMateUnitEquationModel_toTarget hA hB hC₀ hD adj₁ adj₂ α αD₀ K (hu₀ K))
    (fun K => derivedMateUnitEquationModel_toTarget hA hB hC₁ hD adj₁ adj₂ α αD₁ K (hu₁ K))

end CategoryTheory
