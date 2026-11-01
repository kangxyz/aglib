/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionMixedRefinementWhole
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.FamilyModelComparison
public import Aglib.CategoryTheory.Functor.CompositionChoice

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

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The original component square for six independent middle-model families. -/
theorem moduleUnboundedCompactifiedCompositionFamilyComparison_component
    (K : DerivedCategory (ModuleSheaf X Λ)) :
    ((@moduleUnboundedCompactificationFunctor Y Z g Λ _ hY hZ C.targetCompactification (G₀
      C.targetCompactification))).map
      ((moduleUnboundedCompositionFamilyComparison f Λ hX hY F₀ F₁ C.first
        N hN hΛ).hom.app K) ≫
      (moduleUnboundedCompositionFamilyComparison g Λ hY hZ G₀ G₁
        C.targetCompactification N hN hΛ).hom.app
          (((@moduleUnboundedCompactificationFunctor X Y f Λ _ hX hY C.first (F₁ C.first))).obj K) ≫
      (moduleUnboundedCompactifiedCompositionIso f g Λ
        (firstModels := F₁) (secondModels := G₁) (compositeModels := H₁) C N hN hΛ).hom.app K =
    (moduleUnboundedCompactifiedCompositionIso f g Λ
      (firstModels := F₀) (secondModels := G₀) (compositeModels := H₀) C N hN hΛ).hom.app K ≫
      (moduleUnboundedCompositionFamilyComparison (f ≫ g) Λ hX hZ H₀ H₁
        C.composite N hN hΛ).hom.app K := by
  let a : C.Refinement C := ⟨𝟙 _, 𝟙 _, by
    change (𝟙 C.sourceCompactification.Xbar) ≫ C.sourceCompactification.p =
      C.sourceCompactification.p ≫ 𝟙 _
    rw [Category.id_comp, Category.comp_id]⟩
  have ha : a.intermediate = 𝟙 C.first := Subsingleton.elim _ _
  have h := @moduleUnboundedCompactifiedCompositionMixedRefinement_whole X Y Z f g _ _ Λ _
    hX hY hZ C C a (F₁ C.first) (F₀ C.first)
    (G₁ C.targetCompactification) (G₀ C.targetCompactification)
    (H₁ C.composite) (H₀ C.composite)
    (moduleUnboundedCompactifiedCompositionIso f g Λ
      (firstModels := F₀) (secondModels := G₀) (compositeModels := H₀) C N hN hΛ).hom
    (moduleUnboundedCompactifiedCompositionIso f g Λ
      (firstModels := F₁) (secondModels := G₁) (compositeModels := H₁) C N hN hΛ).hom
    (moduleUnboundedCompactifiedCompositionIso_formula f g Λ
      (firstModels := F₀) (secondModels := G₀) (compositeModels := H₀) C N hN hΛ)
    (moduleUnboundedCompactifiedCompositionIso_formula f g Λ
      (firstModels := F₁) (secondModels := G₁) (compositeModels := H₁) C N hN hΛ)
  have hk := congrArg (fun t => t.app K) h
  have hτ := congrArg
    (fun q : C.first ⟶ C.first =>
      @moduleUnboundedCompactificationMixedTransition X Y f _ Λ _ hX hY C.first C.first q
        (F₁ C.first) (F₀ C.first)) ha
  rw [hτ] at hk
  let τf := @moduleUnboundedCompactificationMixedTransition X Y f _ Λ _ hX hY
    C.first C.first (𝟙 C.first) (F₁ C.first) (F₀ C.first)
  let τg := @moduleUnboundedCompactificationMixedTransition Y Z g _ Λ _ hY hZ
    C.targetCompactification C.targetCompactification (𝟙 C.targetCompactification)
    (G₁ C.targetCompactification) (G₀ C.targetCompactification)
  let τh := @moduleUnboundedCompactificationMixedTransition X Z (f ≫ g) _ Λ _ hX hZ
    C.composite C.composite (𝟙 C.composite) (H₁ C.composite) (H₀ C.composite)
  let G := @moduleUnboundedCompactificationFunctor Y Z g Λ _ hY hZ
    C.targetCompactification (G₀ C.targetCompactification)
  let V := @moduleUnboundedCompactificationFunctor X Y f Λ _ hX hY C.first (F₁ C.first)
  change G.map (τf.app K) ≫ τg.app (V.obj K) ≫
      (moduleUnboundedCompactifiedCompositionIso f g Λ
        (firstModels := F₁) (secondModels := G₁) (compositeModels := H₁) C N hN hΛ).hom.app K =
    (moduleUnboundedCompactifiedCompositionIso f g Λ
      (firstModels := F₀) (secondModels := G₀) (compositeModels := H₀) C N hN hΛ).hom.app K ≫
      τh.app K at hk ⊢
  exact hk

/-- Original composition commutes with the actual mixed identity refinements,
without identifying any of the six model families. -/
theorem moduleUnboundedCompactifiedCompositionIso_familyComparison :
    compositionPairIso
        (moduleUnboundedCompositionFamilyComparison f Λ hX hY F₀ F₁ C.first N hN hΛ)
        (moduleUnboundedCompositionFamilyComparison g Λ hY hZ G₀ G₁
          C.targetCompactification N hN hΛ) ≪≫
      (moduleUnboundedCompactifiedCompositionIso f g Λ
        (firstModels := F₁) (secondModels := G₁) (compositeModels := H₁) C N hN hΛ) =
    (moduleUnboundedCompactifiedCompositionIso f g Λ
        (firstModels := F₀) (secondModels := G₀) (compositeModels := H₀) C N hN hΛ) ≪≫
      moduleUnboundedCompositionFamilyComparison (f ≫ g) Λ hX hZ H₀ H₁
        C.composite N hN hΛ := by
  apply Iso.ext
  apply NatTrans.ext
  funext K
  simp only [compositionPairIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Category.assoc]
  exact moduleUnboundedCompactifiedCompositionFamilyComparison_component
    f g Λ F₀ F₁ G₀ G₁ H₀ H₁ C N hN hΛ K

end AlgebraicGeometry.Scheme.EtaleCohomology
