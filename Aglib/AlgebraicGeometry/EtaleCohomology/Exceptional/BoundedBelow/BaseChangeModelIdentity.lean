/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.TargetModelComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.BaseChangeCoherence
public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.BaseChangeTargetModels
public import Aglib.CategoryTheory.Functor.TargetIdentityExchange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.InverseImageModelIdentity

/-!
# Independent-model normalization for identity base change

The source transport below is defined from canonical native target transport
and the original source-isomorphism comparison, never from the base-change map.
The final equation identifies it with the actual independent-model base change.
-/

@[expose] public noncomputable section
open CategoryTheory DerivedCategory.Plus Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wX' wS₀ wS₁ wM wN wR
variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  [Nonempty (Hom.DenseCompactification f)]
local instance : Nonempty (Hom.DenseCompactification (pullback.fst (𝟙 S) f)) :=
  ⟨Hom.DenseCompactification.baseChangeObj (𝟙 S) (moduleExceptionalSuppliedCompactification f)⟩

variable (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hX' : HasDerivedCategory.{wX'} (ModuleSheaf (pullback (𝟙 S) f) Λ))
  (hS₀ : HasDerivedCategory.{wS₀} (ModuleSheaf S Λ))
  (hS₁ : HasDerivedCategory.{wS₁} (ModuleSheaf S Λ))
  (sourceModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))
  (targetModels : ∀ C : Hom.DenseCompactification (pullback.fst (𝟙 S) f),
    HasDerivedCategory.{wN} (ModuleSheaf C.Xbar Λ))

/-- Independently defined source transport normalized by the canonical native equivalence. -/
def moduleExceptionalIdentityModelSourceIso :
    (@moduleExceptionalDirectImagePlusOfNonempty X S f _ Λ _ hX hS₀ (sourceModels
      (moduleExceptionalSuppliedCompactification f))) ⋙
        (canonicalEquivalence hS₀ hS₁).functor ≅
      @moduleDerivedInverseImageTorsion (pullback (𝟙 S) f) X (pullback.snd (𝟙 S) f)
          Λ _ hX' hX ⋙
        (@moduleExceptionalDirectImagePlusOfNonempty (pullback (𝟙 S) f) S (pullback.fst (𝟙 S) f) _
          Λ _ hX' hS₁ (targetModels (moduleExceptionalSuppliedCompactification (pullback.fst (𝟙 S)
          f)))) :=
  Functor.isoWhiskerRight
      (@moduleExceptionalIdentitySourceIsoOfNonempty X S f _ _ Λ _ hX hS₀ hX'
        sourceModels targetModels) (canonicalEquivalence hS₀ hS₁).functor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (@moduleDerivedInverseImageTorsion (pullback (𝟙 S) f) X (pullback.snd (𝟙 S) f)
        Λ _ hX' hX)
      (moduleExceptionalTargetComparison (pullback.fst (𝟙 S) f) Λ
        hX' hS₀ hS₁ targetModels)

/-- The original identity inverse image is normalized before independent source transport. -/
def moduleExceptionalIdentityModelNormalizer :
    (@moduleExceptionalDirectImagePlusOfNonempty X S f _ Λ _ hX hS₀ (sourceModels
      (moduleExceptionalSuppliedCompactification f))) ⋙
        (@Functor.rightDerivedFunctorPlus _ _ _ _ _ _ hS₀ hS₁ (moduleInverseImage (𝟙 S) Λ) _ _) ≅
      @moduleDerivedInverseImageTorsion (pullback (𝟙 S) f) X (pullback.snd (𝟙 S) f)
          Λ _ hX' hX ⋙
        (@moduleExceptionalDirectImagePlusOfNonempty (pullback (𝟙 S) f) S (pullback.fst (𝟙 S) f) _
          Λ _ hX' hS₁ (targetModels (moduleExceptionalSuppliedCompactification (pullback.fst (𝟙 S)
          f)))) :=
  Functor.isoWhiskerLeft _ (moduleDerivedInverseImageModelIdIso S Λ hS₀ hS₁) ≪≫
    moduleExceptionalIdentityModelSourceIso f Λ hX hX' hS₀ hS₁ sourceModels targetModels

variable (rawModels : ∀ C : Hom.DenseCompactification f,
  HasDerivedCategory.{wR} (ModuleSheaf (pullback (𝟙 S) C.p) Λ))

/-- The actual chosen identity base change equals the independently defined source transport,
normalized by the original identity inverse image into canonical native model comparison. -/
theorem moduleExceptionalBaseChange_identity_independentModels :
    @moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty X S S f _ _ (𝟙 S) Λ _
        hX hS₀ hX' hS₁ sourceModels targetModels rawModels =
      moduleExceptionalIdentityModelNormalizer f Λ hX hX' hS₀ hS₁ sourceModels targetModels :=
  targetIdentityExchange_normalized
    (@moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty X S S f _ _ (𝟙 S) Λ _
      hX hS₀ hX' hS₀ sourceModels targetModels rawModels)
    (@moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty X S S f _ _ (𝟙 S) Λ _
      hX hS₀ hX' hS₁ sourceModels targetModels rawModels)
    (Functor.rightDerivedFunctorPlusChangeTarget hS₀ hS₀ hS₁ (moduleInverseImage (𝟙 S) Λ))
    (moduleExceptionalTargetComparison (pullback.fst (𝟙 S) f) Λ hX' hS₀ hS₁ targetModels)
    (@moduleDerivedInverseImageIdIso Λ _ S hS₀)
    (moduleDerivedInverseImageModelIdIso S Λ hS₀ hS₁)
    (@moduleExceptionalIdentitySourceIsoOfNonempty X S f _ _ Λ _ hX hS₀ hX'
      sourceModels targetModels)
    (imageTargetIso ((@moduleExceptionalDirectImagePlusOfNonempty X S f _ Λ _ hX hS₀ (sourceModels
      (moduleExceptionalSuppliedCompactification f))))
      (Functor.rightDerivedFunctorPlusChangeTarget hS₀ hS₀ hS₁ (moduleInverseImage (𝟙 S) Λ)))
    rfl
    (identityFunctorNormalizer
      ((@moduleExceptionalDirectImagePlusOfNonempty X S f _ Λ _ hX hS₀ (sourceModels
        (moduleExceptionalSuppliedCompactification f))))
      (@moduleDerivedInverseImageIdIso Λ _ S hS₀)) rfl rfl
    (@moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty_identity X S f _ _ Λ _
      hX hS₀ hX' sourceModels targetModels rawModels)
    (moduleExceptionalBaseChange_targetModel f (𝟙 S) Λ hX hS₀ hX' hS₀ hS₁
      sourceModels targetModels rawModels)

end AlgebraicGeometry.Scheme.EtaleCohomology
