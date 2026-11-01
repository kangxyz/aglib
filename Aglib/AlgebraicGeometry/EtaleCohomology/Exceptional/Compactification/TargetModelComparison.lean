/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.Diagram
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.DirectImageTargetModels

/-! # Target-model transport of the original compactification refinement diagram -/

@[expose] public noncomputable section
open CategoryTheory DerivedCategory.Plus

namespace CategoryTheory
variable {U A B T₀ T₁ : Type*}
  [Category* U] [Category* A] [Category* B] [Category* T₀] [Category* T₁]

/-- Postcomposition transport through an unchanged first factor. -/
def imageTargetIso (L : U ⥤ A) {R₀ : A ⥤ T₀} {R₁ : A ⥤ T₁}
    {E : T₀ ⥤ T₁} (t : R₀ ⋙ E ≅ R₁) : (L ⋙ R₀) ⋙ E ≅ L ⋙ R₁ :=
  Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft L t

/-- Original image comparisons retain their maps under a coherent target transport. -/
theorem imageComparison_target
    {L₁ : U ⥤ A} {L₂ : U ⥤ B} {F : A ⥤ B}
    {R₁₀ : A ⥤ T₀} {R₂₀ : B ⥤ T₀} {R₁₁ : A ⥤ T₁} {R₂₁ : B ⥤ T₁}
    {E : T₀ ⥤ T₁} (δ : L₂ ⟶ L₁ ⋙ F)
    (e₀ : F ⋙ R₂₀ ≅ R₁₀) (e₁ : F ⋙ R₂₁ ≅ R₁₁)
    (t₁ : R₁₀ ⋙ E ≅ R₁₁) (t₂ : R₂₀ ⋙ E ≅ R₂₁)
    (he : Functor.isoWhiskerRight e₀ E ≪≫ t₁ =
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft F t₂ ≪≫ e₁) :
    Functor.whiskerRight (imageComparison δ e₀) E ≫ (imageTargetIso L₁ t₁).hom =
      (imageTargetIso L₂ t₂).hom ≫ imageComparison δ e₁ := by
  apply NatTrans.ext
  funext K
  have heK := congrArg (fun z => z.hom.app (L₁.obj K)) he
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp] at heK
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, imageComparison_app,
    imageTargetIso, Iso.trans_hom, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Category.id_comp, Functor.map_comp]
  rw [Category.assoc, heK, ← Category.assoc]
  simpa only [Functor.comp_map, Functor.comp_obj, Category.assoc] using congrArg
    (fun z => z ≫ e₁.hom.app (L₁.obj K)) (t₂.hom.naturality (δ.app K))
end CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS₀ wS₁ wM
variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hS₀ : HasDerivedCategory.{wS₀} (ModuleSheaf S Λ))
  (hS₁ : HasDerivedCategory.{wS₁} (ModuleSheaf S Λ))
  (models : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))

/-- Canonical native target transport of the actual compactification value. -/
def moduleCompactificationTargetComparison (C : Hom.DenseCompactification f) :
    (@moduleCompactificationFunctor X S f Λ _ hX hS₀ C (models C)) ⋙
        (canonicalEquivalence hS₀ hS₁).functor ≅
      (@moduleCompactificationFunctor X S f Λ _ hX hS₁ C (models C)) :=
  imageTargetIso ((@moduleTorsionCohomologyPlus X Λ _ hX).ι ⋙
    @moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX (models C))
    (moduleDerivedDirectImageTargetIso Λ (models C) hS₀ hS₁ C.p)

/-- Canonical target transport is natural for the unchanged original refinement transitions. -/
theorem moduleCompactificationTargetComparison_naturality
    {C D : Hom.DenseCompactification f} (a : C ⟶ D) :
    Functor.whiskerRight (@moduleCompactificationTransition X S f _ Λ _ hX hS₀ models C D a)
        (canonicalEquivalence hS₀ hS₁).functor ≫
      (moduleCompactificationTargetComparison f Λ hX hS₀ hS₁ models C).hom =
    (moduleCompactificationTargetComparison f Λ hX hS₀ hS₁ models D).hom ≫
      @moduleCompactificationTransition X S f _ Λ _ hX hS₁ models C D a := by
  have h := imageComparison_target
    (L₁ := (@moduleTorsionCohomologyPlus X Λ _ hX).ι ⋙
      @moduleDerivedLowerShriek X C.Xbar C.j _ Λ _ hX (models C))
    (L₂ := (@moduleTorsionCohomologyPlus X Λ _ hX).ι ⋙
      @moduleDerivedLowerShriek X D.Xbar D.j _ Λ _ hX (models D))
    (F := (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ (models C) (models D) (moduleDirectImage
      a.hom Λ) _ _))
    (Functor.whiskerLeft (@moduleTorsionCohomologyPlus X Λ _ hX).ι
      (@moduleDerivedRefinementComparison X S f _ C D a Λ _ hX (models C) (models D)))
    (@moduleDerivedRefinementDirectImageIso Λ _ X S f hS₀ C D a (models C) (models D))
    (@moduleDerivedRefinementDirectImageIso Λ _ X S f hS₁ C D a (models C) (models D))
    (moduleDerivedDirectImageTargetIso Λ (models C) hS₀ hS₁ C.p)
    (moduleDerivedDirectImageTargetIso Λ (models D) hS₀ hS₁ D.p)
    (moduleDerivedDirectImageTargetIso_over Λ (models C) (models D) hS₀ hS₁
      C.p D.p a.hom a.base_fac)
  exact h

end AlgebraicGeometry.Scheme.EtaleCohomology
