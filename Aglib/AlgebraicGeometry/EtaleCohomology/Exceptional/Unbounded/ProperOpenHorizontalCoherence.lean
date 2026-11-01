/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperOpenMate
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenComparisonPasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.LowerShriekCompositionConjugacy
public import Aglib.CategoryTheory.Adjunction.MatePastingIdentification

/-! # Horizontal pasting of the original proper/open mate

Reflect original inverse-image square pasting through the actual open
adjunctions and original conjugate lower-shriek compositors, then take the
original proper-map mates. No desired open-square pasting is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

private theorem forward_horizontal_of_inverse_vertical
    {A B C D E F : Type*}
    [Category A] [Category B] [Category C] [Category D] [Category E] [Category F]
    {J₁ : B ⥤ A} {J₂ : C ⥤ B} {I₁ : E ⥤ D} {I₂ : F ⥤ E}
    {P₀ : A ⥤ D} {P₁ : B ⥤ E} {P₂ : C ⥤ F} {J : C ⥤ A} {I : F ⥤ D}
    (e₁ : J₁ ⋙ P₀ ≅ P₁ ⋙ I₁) (e₂ : J₂ ⋙ P₁ ≅ P₂ ⋙ I₂)
    (e : J ⋙ P₀ ≅ P₂ ⋙ I) (cJ : J ≅ J₂ ⋙ J₁) (cI : I ≅ I₂ ⋙ I₁)
    (h : ∀ K, VerticalSquareEquation
      (TwoSquare.mk _ _ _ _ e₂.inv) (TwoSquare.mk _ _ _ _ e₁.inv)
      (TwoSquare.mk _ _ _ _ e.inv) cJ cI K) (K : C) :
    HorizontalSquareEquation
      (TwoSquare.mk _ _ _ _ e₂.hom) (TwoSquare.mk _ _ _ _ e₁.hom)
      (TwoSquare.mk _ _ _ _ e.hom) cJ.hom cI.hom K := by
  have hh := congrArg (fun a => e.hom.app K ≫ a ≫ e₁.hom.app (J₂.obj K) ≫
    I₁.map (e₂.hom.app K)) (h K)
  dsimp only [VerticalSquareEquation, HorizontalSquareEquation, TwoSquare.mk,
    TwoSquare.natTrans, Functor.comp_obj] at hh ⊢
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, Iso.hom_inv_id_app_assoc,
    ← I₁.map_comp, Iso.inv_hom_id_app] at hh
  rw [I₁.map_id ((P₂ ⋙ I₂).obj K)] at hh
  change e.hom.app K ≫ cI.hom.app (P₂.obj K) ≫
      𝟙 ((I₂ ⋙ I₁).obj (P₂.obj K)) = _ at hh
  rw [Category.comp_id (cI.hom.app (P₂.obj K))] at hh
  exact hh.symm

universe u wU₀ wU₁ wU₂ wX₀ wX₁ wX₂

variable (Λ : Type (u + 1)) [Ring Λ]
  {U₀ U₁ U₂ X₀ X₁ X₂ : Scheme.{u}}
  (j₁ : U₁ ⟶ U₀) (j₂ : U₂ ⟶ U₁) (i₁ : X₁ ⟶ X₀) (i₂ : X₂ ⟶ X₁)
  (f₀ : X₀ ⟶ U₀) (f₁ : X₁ ⟶ U₁) (f₂ : X₂ ⟶ U₂)
  [Etale j₁] [Etale j₂] [Etale i₁] [Etale i₂]
  (h₁ : IsPullback f₁ i₁ j₁ f₀) (h₂ : IsPullback f₂ i₂ j₂ f₁)
  (ht : IsPullback f₂ (i₂ ≫ i₁) (j₂ ≫ j₁) f₀)
  [HasDerivedCategory.{wU₀} (ModuleSheaf U₀ Λ)]
  [HasDerivedCategory.{wU₁} (ModuleSheaf U₁ Λ)]
  [HasDerivedCategory.{wU₂} (ModuleSheaf U₂ Λ)]
  [HasDerivedCategory.{wX₀} (ModuleSheaf X₀ Λ)]
  [HasDerivedCategory.{wX₁} (ModuleSheaf X₁ Λ)]
  [HasDerivedCategory.{wX₂} (ModuleSheaf X₂ Λ)]

private theorem inverse_openComparison_hComp
    (K : DerivedCategory (ModuleSheaf U₂ Λ)) :
    VerticalSquareEquation
      (TwoSquare.mk _ _ _ _
        (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso f₂ i₂ j₂ f₁ h₂ Λ).inv)
      (TwoSquare.mk _ _ _ _
        (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso f₁ i₁ j₁ f₀ h₁ Λ).inv)
      (TwoSquare.mk _ _ _ _
        (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso f₂ (i₂ ≫ i₁) (j₂ ≫ j₁) f₀ ht
      Λ).inv)
      (moduleUnboundedDerivedLowerShriekCompIso Λ j₁ j₂)
      (moduleUnboundedDerivedLowerShriekCompIso Λ i₁ i₂) K := by
  exact verticalSquareEquation_of_identified_mates
    (TwoSquare.mk _ _ _ _
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso f₂ i₂ j₂ f₁ h₂ Λ).inv)
    (TwoSquare.mk _ _ _ _
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso f₁ i₁ j₁ f₀ h₁ Λ).inv)
    (TwoSquare.mk _ _ _ _
      (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso f₂ (i₂ ≫ i₁) (j₂ ≫ j₁) f₀ ht Λ).inv)
    (moduleUnboundedDerivedLowerShriekCompIso Λ j₁ j₂)
    (moduleUnboundedDerivedLowerShriekCompIso Λ i₁ i₂)
    (moduleUnboundedDerivedInverseImageCompIso Λ j₁ j₂)
    (moduleUnboundedDerivedInverseImageCompIso Λ i₁ i₂)
    (moduleUnboundedDerivedLowerShriekAdjunction j₂ Λ)
      (moduleUnboundedDerivedLowerShriekAdjunction i₂ Λ)
    (moduleUnboundedDerivedLowerShriekAdjunction j₁ Λ)
      (moduleUnboundedDerivedLowerShriekAdjunction i₁ Λ)
    (moduleUnboundedDerivedLowerShriekAdjunction (j₂ ≫ j₁) Λ)
    (moduleUnboundedDerivedLowerShriekAdjunction (i₂ ≫ i₁) Λ)
    (conjugateEquiv_moduleUnboundedDerivedLowerShriekCompIso_hom Λ j₁ j₂)
    (conjugateEquiv_moduleUnboundedDerivedLowerShriekCompIso_hom Λ i₁ i₂)
    (TwoSquare.mk _ _ _ _
      (moduleUnboundedDerivedInverseImageSquareIso Λ f₁ f₂ j₂ i₂ h₂.w).hom)
    (TwoSquare.mk _ _ _ _
      (moduleUnboundedDerivedInverseImageSquareIso Λ f₀ f₁ j₁ i₁ h₁.w).hom)
    (TwoSquare.mk _ _ _ _
      (moduleUnboundedDerivedInverseImageSquareIso Λ f₀ f₂ (j₂ ≫ j₁) (i₂ ≫ i₁) ht.w).hom)
    (mateEquiv_moduleUnboundedDerivedOpenComparison_inv f₂ i₂ j₂ f₁ h₂ Λ)
    (mateEquiv_moduleUnboundedDerivedOpenComparison_inv f₁ i₁ j₁ f₀ h₁ Λ)
    (mateEquiv_moduleUnboundedDerivedOpenComparison_inv f₂ (i₂ ≫ i₁) (j₂ ≫ j₁) f₀ ht Λ)
    (moduleUnboundedDerivedInverseImageSquareIso_hComp Λ f₀ f₁ f₂ j₁ j₂ i₁ i₂
      h₁.w h₂.w ht.w) K

/-- Actual horizontal open-comparison coherence, reflected from the canonical
inverse-image squares rather than postulated for the lower-shriek maps. -/
theorem moduleUnboundedDerivedOpenComparison_hComp
    (K : DerivedCategory (ModuleSheaf U₂ Λ)) :
    HorizontalSquareEquation
      (TwoSquare.mk _ _ _ _
        (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso f₂ i₂ j₂ f₁ h₂ Λ).hom)
      (TwoSquare.mk _ _ _ _
        (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso f₁ i₁ j₁ f₀ h₁ Λ).hom)
      (TwoSquare.mk _ _ _ _
        (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso f₂ (i₂ ≫ i₁) (j₂ ≫ j₁) f₀ ht
      Λ).hom)
      (moduleUnboundedDerivedLowerShriekCompIso Λ j₁ j₂).hom
      (moduleUnboundedDerivedLowerShriekCompIso Λ i₁ i₂).hom K :=
  forward_horizontal_of_inverse_vertical
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso f₁ i₁ j₁ f₀ h₁ Λ)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso f₂ i₂ j₂ f₁ h₂ Λ)
    (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso f₂ (i₂ ≫ i₁) (j₂ ≫ j₁) f₀ ht Λ)
    (moduleUnboundedDerivedLowerShriekCompIso Λ j₁ j₂)
    (moduleUnboundedDerivedLowerShriekCompIso Λ i₁ i₂)
    (inverse_openComparison_hComp Λ j₁ j₂ i₁ i₂ f₀ f₁ f₂ h₁ h₂ ht) K

/-- Horizontal pasting of the actual global proper/open mixed mates. -/
theorem moduleUnboundedProperOpenMate_hComp
    (K : DerivedCategory (ModuleSheaf X₂ Λ)) :
    HorizontalMateEquation
      (TwoSquare.mk _ _ _ _
        (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso f₂ i₂ j₂ f₁ h₂ Λ).hom)
      (TwoSquare.mk _ _ _ _
        (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso f₁ i₁ j₁ f₀ h₁ Λ).hom)
      (TwoSquare.mk _ _ _ _
        (moduleUnboundedDerivedLowerShriekCartesianBaseChangeIso f₂ (i₂ ≫ i₁) (j₂ ≫ j₁) f₀ ht
      Λ).hom)
      (moduleUnboundedDerivedLowerShriekCompIso Λ j₁ j₂).hom
      (moduleUnboundedDerivedLowerShriekCompIso Λ i₁ i₂).hom
      (moduleUnboundedDerivedAdjunction Λ f₂) (moduleUnboundedDerivedAdjunction Λ f₁)
      (moduleUnboundedDerivedAdjunction Λ f₀) K :=
  horizontalMateEquation _ _ _ _ _
    (moduleUnboundedDerivedAdjunction Λ f₂) (moduleUnboundedDerivedAdjunction Λ f₁)
    (moduleUnboundedDerivedAdjunction Λ f₀)
    (moduleUnboundedDerivedOpenComparison_hComp Λ j₁ j₂ i₁ i₂ f₀ f₁ f₂ h₁ h₂ ht) K

end AlgebraicGeometry.Scheme.EtaleCohomology
