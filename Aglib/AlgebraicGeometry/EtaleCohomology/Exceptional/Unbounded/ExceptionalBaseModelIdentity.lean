/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.NormalizedBaseIdentityModel
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ExceptionalBaseChangeIdentity

/-! # Original chosen identity base change between independent base derived models -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

private theorem base_identity_postcomp
    {A B₀ B₁ A' : Type*} [Category* A] [Category* B₀] [Category* B₁] [Category* A']
    {F₀ : A ⥤ B₀} {F₁ : A ⥤ B₁} {G : B₀ ⥤ B₁} {V : A ⥤ A'}
    {D T : A' ⥤ B₁}
    (β : F₀ ⋙ G ≅ V ⋙ D) (e : F₀ ⋙ G ≅ F₁)
    (s : F₁ ≅ V ⋙ D) (c : D ≅ T) (h : β = e ≪≫ s) :
    β ≪≫ Functor.isoWhiskerLeft V c =
      e ≪≫ (s ≪≫ Functor.isoWhiskerLeft V c) := by
  rw [h, Iso.trans_assoc]

universe u wX wS₀ wS₁ wX' wM wD wR
variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  [Nonempty (Hom.DenseCompactification f)]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  (hS₀ : HasDerivedCategory.{wS₀} (ModuleSheaf S Λ))
  [hS₁ : HasDerivedCategory.{wS₁} (ModuleSheaf S Λ)]
  [hX' : HasDerivedCategory.{wX'} (ModuleSheaf (pullback (𝟙 S) f) Λ)]
  [sourceModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [targetModels : ∀ C : Hom.DenseCompactification (pullback.fst (𝟙 S) f),
    HasDerivedCategory.{wD} (ModuleSheaf C.Xbar Λ)]

local instance exceptionalBaseIdentityNonempty :
    Nonempty (Hom.DenseCompactification (pullback.fst (𝟙 S) f)) :=
  ⟨Hom.DenseCompactification.baseChangeObj (𝟙 S) (moduleExceptionalSuppliedCompactification f)⟩

omit hX' targetModels in
/-- Chosen base-model transport uses only the original proper-image target comparison
at the existing chosen geometric compactification, not the base-change map. -/
def moduleExceptionalDirectImageUnboundedChangeBaseModel :
    (@moduleExceptionalDirectImageUnboundedOfNonempty X S f _ Λ _ hX hS₀ (sourceModels
      (moduleExceptionalSuppliedCompactification f))) ⋙
        (moduleUnboundedBaseModelEquivalence Λ S hS₀ hS₁).functor ≅
      moduleExceptionalDirectImageUnboundedOfNonempty f Λ :=
  moduleUnboundedRawCompactificationChangeBaseModel
    (moduleExceptionalSuppliedCompactification f).toCompactification Λ hX hS₀ hS₁
    (sourceModels (moduleExceptionalSuppliedCompactification f))

omit hX' targetModels in
/-- The identity normalizer is the original inverse-image comparison to localization
transport followed by the original chosen proper-image target comparison. -/
def moduleExceptionalDirectImageUnboundedBaseIdentityNormalizer :
    (@moduleExceptionalDirectImageUnboundedOfNonempty X S f _ Λ _ hX hS₀ (sourceModels
      (moduleExceptionalSuppliedCompactification f))) ⋙
        @moduleUnboundedDerivedInverseImage Λ _ S S (𝟙 S) hS₀ hS₁ ≅
      moduleExceptionalDirectImageUnboundedOfNonempty f Λ :=
  Functor.isoWhiskerLeft _
    (moduleUnboundedDerivedInverseImageIdentityModelIso Λ S hS₀ hS₁) ≪≫
    moduleExceptionalDirectImageUnboundedChangeBaseModel f Λ hS₀

variable [rawModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wR} (ModuleSheaf (pullback (𝟙 S) C.p) Λ)]
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

omit [Nonempty (Hom.DenseCompactification f)] in
/-- The independent-base identity equation at any actual source and target model. -/
theorem moduleUnboundedCompactificationBaseChangeIsoTo_identity_baseModel
    (C : Hom.DenseCompactification f)
    (D : Hom.DenseCompactification (pullback.fst (𝟙 S) f)) :
    (@moduleUnboundedCompactificationBaseChangeIsoTo X S S f _ (𝟙 S) Λ _ hX hS₀ hX' hS₁
      targetModels N hN hΛ C D (sourceModels C) (rawModels C)) =
      moduleUnboundedRawCompactificationBaseIdentityIso C.toCompactification
        Λ hX hS₀ hS₁ (sourceModels C) ≪≫
      moduleUnboundedIdentitySourceModelIsoTo f Λ N hN hΛ C D :=
  base_identity_postcomp
    (@moduleUnboundedNormalizedBaseIdentityModelIso X S f _ C Λ _
      hX hS₀ hS₁ (sourceModels C) hX' (rawModels C)
      (targetModels (Hom.DenseCompactification.baseChangeObj (𝟙 S) C)) N hN hΛ)
    _ (moduleUnboundedIdentitySourceModelIso C Λ N hN hΛ)
    (moduleUnboundedCompactificationComparison (pullback.fst (𝟙 S) f) Λ N hN hΛ
      (Hom.DenseCompactification.baseChangeObj (𝟙 S) C) D)
    (moduleUnboundedNormalizedBaseIdentityModelIso_eq C Λ hS₀ N hN hΛ)

/-- The actual chosen identity exchange retains two independent base derived models.
Its normalizer and source comparison are independently defined from the original maps. -/
theorem moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty_identity_baseModel :
    (@moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty X S S f _ _ (𝟙 S) Λ _ hX hS₀
      hX' hS₁ targetModels N hN hΛ (sourceModels (moduleExceptionalSuppliedCompactification f))
      (rawModels (moduleExceptionalSuppliedCompactification f))) =
      moduleExceptionalDirectImageUnboundedBaseIdentityNormalizer f Λ hS₀ ≪≫
        moduleExceptionalUnboundedIdentitySourceIsoOfNonempty f Λ N hN hΛ :=
  moduleUnboundedCompactificationBaseChangeIsoTo_identity_baseModel f Λ hS₀ N hN hΛ
    (moduleExceptionalSuppliedCompactification f)
    (moduleExceptionalSuppliedCompactification (pullback.fst (𝟙 S) f))

end AlgebraicGeometry.Scheme.EtaleCohomology
