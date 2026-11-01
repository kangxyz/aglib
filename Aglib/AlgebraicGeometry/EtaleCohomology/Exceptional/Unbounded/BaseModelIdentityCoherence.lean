/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ExceptionalBaseModelIdentity

/-! # Actual source-model coherence of the original independent-base normalizer -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

private theorem base_normalizer_square
    {A B₀ B₁ A' : Type*} [Category* A] [Category* B₀] [Category* B₁] [Category* A']
    {F₀ M₀ : A ⥤ B₀} {F₁ M₁ : A ⥤ B₁} {G : B₀ ⥤ B₁} {V : A ⥤ A'}
    {D T : A' ⥤ B₁}
    (c₀ : F₀ ≅ M₀) (c₁ : F₁ ≅ M₁) (d : D ≅ T)
    (e : F₀ ⋙ G ≅ F₁) (eM : M₀ ⋙ G ≅ M₁)
    (s : F₁ ≅ V ⋙ D) (sM : M₁ ≅ V ⋙ T)
    (β : F₀ ⋙ G ≅ V ⋙ D) (βM : M₀ ⋙ G ≅ V ⋙ T)
    (h : Functor.isoWhiskerRight c₀ G ≪≫ βM = β ≪≫ Functor.isoWhiskerLeft V d)
    (he : β = e ≪≫ s) (heM : βM = eM ≪≫ sM)
    (hs : c₁ ≪≫ sM = s ≪≫ Functor.isoWhiskerLeft V d) :
    Functor.isoWhiskerRight c₀ G ≪≫ eM = e ≪≫ c₁ := by
  apply Iso.ext
  apply (cancel_mono sM.hom).1
  rw [he, heM] at h
  have hh := congrArg Iso.hom h
  have hsH := congrArg Iso.hom hs
  simp only [Iso.trans_hom, Category.assoc] at hh ⊢
  simp only [Iso.trans_hom] at hsH
  rw [← hsH] at hh
  exact hh


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
  [rawModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wR} (ModuleSheaf (pullback (𝟙 S) C.p) Λ)]
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

local instance baseNormalizerCoherenceNonempty :
    Nonempty (Hom.DenseCompactification (pullback.fst (𝟙 S) f)) :=
  ⟨Hom.DenseCompactification.baseChangeObj (𝟙 S) (moduleExceptionalSuppliedCompactification f)⟩

/-- The original base-model identity normalizer intertwines the actual canonical
compactification comparisons; its definition remains independent of base change. -/
theorem moduleExceptionalDirectImageUnboundedBaseIdentityNormalizer_model
    (C : Hom.DenseCompactification f)
    (D : Hom.DenseCompactification (pullback.fst (𝟙 S) f)) :
    Functor.isoWhiskerRight
        (@moduleExceptionalDirectImageUnboundedOfNonemptyIso X S f _ _ Λ _
          hX hS₀ sourceModels N hN hΛ C)
        (@moduleUnboundedDerivedInverseImage Λ _ S S (𝟙 S) hS₀ hS₁) ≪≫
      moduleUnboundedRawCompactificationBaseIdentityIso C.toCompactification
        Λ hX hS₀ hS₁ (sourceModels C) =
    moduleExceptionalDirectImageUnboundedBaseIdentityNormalizer f Λ hS₀ ≪≫
      moduleExceptionalDirectImageUnboundedOfNonemptyIso f Λ N hN hΛ C := by
  exact base_normalizer_square
    (@moduleExceptionalDirectImageUnboundedOfNonemptyIso X S f _ _ Λ _
      hX hS₀ sourceModels N hN hΛ C)
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso f Λ N hN hΛ C)
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso (pullback.fst (𝟙 S) f) Λ N hN hΛ D)
    (moduleExceptionalDirectImageUnboundedBaseIdentityNormalizer f Λ hS₀)
    (moduleUnboundedRawCompactificationBaseIdentityIso C.toCompactification
      Λ hX hS₀ hS₁ (sourceModels C))
    (moduleExceptionalUnboundedIdentitySourceIsoOfNonempty f Λ N hN hΛ)
    (moduleUnboundedIdentitySourceModelIsoTo f Λ N hN hΛ C D)
    ((@moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty X S S f _ _ (𝟙 S) Λ _ hX hS₀
      hX' hS₁ targetModels N hN hΛ (sourceModels (moduleExceptionalSuppliedCompactification f))
      (rawModels (moduleExceptionalSuppliedCompactification f))))
    ((@moduleUnboundedCompactificationBaseChangeIsoTo X S S f _ (𝟙 S) Λ _ hX hS₀ hX' hS₁
      targetModels N hN hΛ C D (sourceModels C) (rawModels C)))
    ((@moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty_model X S S f _ _ (𝟙 S) Λ _ hX
      hS₀ hX' hS₁ targetModels N hN hΛ sourceModels rawModels C D))
    (moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty_identity_baseModel
      f Λ hS₀ N hN hΛ)
    (moduleUnboundedCompactificationBaseChangeIsoTo_identity_baseModel f Λ hS₀ N hN hΛ C D)
    (moduleExceptionalUnboundedIdentitySourceIsoOfNonempty_model f Λ N hN hΛ C D)

end AlgebraicGeometry.Scheme.EtaleCohomology
