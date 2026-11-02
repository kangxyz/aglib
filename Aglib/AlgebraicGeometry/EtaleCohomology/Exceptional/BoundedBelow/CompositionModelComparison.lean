/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionMixedRefinementWhole
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.FamilyModelComparison
public import Aglib.CategoryTheory.Functor.CompositionChoice
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.CompositionRefinementAdapters

/-! # Original composition comparison under independent changes of middle models

The comparison is the original mixed identity refinement at each of the three
ambients. All six model families remain independent. The actual composition
map is unchanged; the cube is supplied by its original unit, mate and image faces.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wY wZ wF₀ wF₁ wG₀ wG₁ wH₀ wH₁

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  [QuasiCompact f] [QuasiCompact g] (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hY : HasDerivedCategory.{wY} (ModuleSheaf Y Λ)]
  [hZ : HasDerivedCategory.{wZ} (ModuleSheaf Z Λ)]
  (F₀ : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wF₀} (ModuleSheaf C.Xbar Λ))
  (F₁ : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wF₁} (ModuleSheaf C.Xbar Λ))
  (G₀ : ∀ C : Hom.DenseCompactification g,
    HasDerivedCategory.{wG₀} (ModuleSheaf C.Xbar Λ))
  (G₁ : ∀ C : Hom.DenseCompactification g,
    HasDerivedCategory.{wG₁} (ModuleSheaf C.Xbar Λ))
  (H₀ : ∀ C : Hom.DenseCompactification (f ≫ g),
    HasDerivedCategory.{wH₀} (ModuleSheaf C.Xbar Λ))
  (H₁ : ∀ C : Hom.DenseCompactification (f ≫ g),
    HasDerivedCategory.{wH₁} (ModuleSheaf C.Xbar Λ))
  (C : Hom.CompactifiedComposition f g)

/-- The original component square before imposing the target torsion property. -/
theorem moduleCompactifiedCompositionFamilyComparison_component
    (K : (moduleTorsionCohomologyPlus X Λ).FullSubcategory) :
    (@moduleDerivedDirectImage Z Λ _ C.targetCompactification.Xbar
      C.targetCompactification.p hZ (G₀ C.targetCompactification)).map
      ((@moduleDerivedLowerShriek Y C.targetCompactification.Xbar
        C.targetCompactification.j _ Λ _ hY (G₀ C.targetCompactification)).map
        ((moduleCompactificationFamilyComparison f Λ hX hY F₀ F₁ C.first).hom.app K)) ≫
      (moduleCompactificationFamilyComparison g Λ hY hZ G₀ G₁
        C.targetCompactification).hom.app
          (((@moduleCompactificationTorsionFunctor _ _ f Λ _ hX hY C.first (F₁ C.first))).obj K) ≫
      (moduleCompactifiedCompositionAmbientIso f g Λ
        (firstModels := F₁) (secondModels := G₁) (compositeModels := H₁) C).hom.app K =
    (moduleCompactifiedCompositionAmbientIso f g Λ
      (firstModels := F₀) (secondModels := G₀) (compositeModels := H₀) C).hom.app K ≫
      (moduleCompactificationFamilyComparison (f ≫ g) Λ hX hZ H₀ H₁ C.composite).hom.app K := by
  let a : C.Refinement C := ⟨𝟙 _, 𝟙 _, by
    change (𝟙 C.sourceCompactification.Xbar) ≫ C.sourceCompactification.p =
      C.sourceCompactification.p ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]⟩
  have ha : a.intermediate = 𝟙 C.first := Subsingleton.elim _ _
  have h := @moduleCompactifiedCompositionMixedRefinement_whole X Y Z f g _ _ Λ _
    hX hY hZ C C a (F₁ C.first) (F₀ C.first)
    (G₁ C.targetCompactification) (G₀ C.targetCompactification)
    (H₁ C.composite) (H₀ C.composite)
    (moduleCompactifiedCompositionAmbientIso f g Λ
      (firstModels := F₀) (secondModels := G₀) (compositeModels := H₀) C).hom
    (moduleCompactifiedCompositionAmbientIso f g Λ
      (firstModels := F₁) (secondModels := G₁) (compositeModels := H₁) C).hom
    (moduleCompactifiedCompositionAmbientIso_formula f g Λ
      (firstModels := F₀) (secondModels := G₀) (compositeModels := H₀) (C := C))
    (moduleCompactifiedCompositionAmbientIso_formula f g Λ
      (firstModels := F₁) (secondModels := G₁) (compositeModels := H₁) (C := C))
  have hk := congrArg (fun t => t.app K) h
  have hτ := congrArg
    (fun q : C.first ⟶ C.first =>
      @moduleCompactificationMixedTransition X Y f _ Λ _ hX hY C.first C.first q
        (F₁ C.first) (F₀ C.first)) ha
  rw [hτ] at hk
  let τf := @moduleCompactificationMixedTransition X Y f _ Λ _ hX hY
    C.first C.first (𝟙 C.first) (F₁ C.first) (F₀ C.first)
  let δg := @moduleDerivedRefinementComparison Y Z g _ C.targetCompactification
    C.targetCompactification (𝟙 C.targetCompactification) Λ _ hY
    (G₁ C.targetCompactification) (G₀ C.targetCompactification)
  let eg := @moduleDerivedRefinementDirectImageIso Λ _ Y Z g hZ
    C.targetCompactification C.targetCompactification (𝟙 C.targetCompactification)
    (G₁ C.targetCompactification) (G₀ C.targetCompactification)
  let τh := @moduleCompactificationMixedTransition X Z (f ≫ g) _ Λ _ hX hZ
    C.composite C.composite (𝟙 C.composite) (H₁ C.composite) (H₀ C.composite)
  let R := @moduleDerivedDirectImage Z Λ _ C.targetCompactification.Xbar
    C.targetCompactification.p hZ (G₀ C.targetCompactification)
  let I := @moduleDerivedLowerShriek Y C.targetCompactification.Xbar
    C.targetCompactification.j _ Λ _ hY (G₀ C.targetCompactification)
  let V := @moduleCompactificationFunctor X Y f Λ _ hX hY C.first (F₁ C.first)
  change R.map (I.map (τf.app K)) ≫
      (CategoryTheory.imageComparison δg eg).app (V.obj K) ≫
      (moduleCompactifiedCompositionAmbientIso f g Λ
        (firstModels := F₁) (secondModels := G₁) (compositeModels := H₁) C).hom.app K =
    (moduleCompactifiedCompositionAmbientIso f g Λ
      (firstModels := F₀) (secondModels := G₀) (compositeModels := H₀) C).hom.app K ≫
      τh.app K at hk ⊢
  exact hk


/-- The original supplied-tower composition commutes with the original six-family
model comparison. No mixed identity refinement is replaced by an identity map. -/
theorem moduleCompactifiedCompositionIso_familyComparison :
    compositionPairIso
        (moduleCompactificationTorsionFamilyComparison f Λ hX hY F₀ F₁ C.first)
        (moduleCompactificationTorsionFamilyComparison g Λ hY hZ G₀ G₁
          C.targetCompactification) ≪≫
      (moduleCompactifiedCompositionIso f g Λ
        (firstModels := F₁) (secondModels := G₁) (compositeModels := H₁) C) =
    (moduleCompactifiedCompositionIso f g Λ
        (firstModels := F₀) (secondModels := G₀) (compositeModels := H₀) C) ≪≫
      moduleCompactificationTorsionFamilyComparison (f ≫ g) Λ hX hZ H₀ H₁ C.composite := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  apply ObjectProperty.hom_ext
  simp only [compositionPairIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app,
    ObjectProperty.FullSubcategory.comp_hom, Category.assoc]
  exact moduleCompactifiedCompositionFamilyComparison_component f g Λ F₀ F₁ G₀ G₁ H₀ H₁ C K

end AlgebraicGeometry.Scheme.EtaleCohomology
