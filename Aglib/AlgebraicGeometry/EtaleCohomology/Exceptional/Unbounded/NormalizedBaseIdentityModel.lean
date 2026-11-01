/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawBaseIdentityModel

/-! # Actual normalized identity exchange through original base-model transport -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

private theorem regroup_base_identity
    {D : Type*} [Category* D] {A B C E F : D}
    (a : A ≅ B) (b : B ≅ C) (c : C ≅ E) (s : E ≅ F)
    (θ : A ⟶ F) (h : θ = (a ≪≫ b ≪≫ c ≪≫ s).hom) :
    θ = ((a ≪≫ (b ≪≫ c)) ≪≫ s).hom := by
  simpa only [Iso.trans_hom, Category.assoc] using h

private theorem normalize_base_identity
    {A B₀ B₁ A' : Type*} [Category* A] [Category* B₀] [Category* B₁] [Category* A']
    {F₀ : A ⥤ B₀} {F₁ : A ⥤ B₁} {G : B₀ ⥤ B₁} {V : A ⥤ A'}
    {R D T : A' ⥤ B₁}
    (δ : F₀ ⟶ F₀) (βr : F₀ ⋙ G ⟶ V ⋙ R) (θ : F₀ ⋙ G ⟶ V ⋙ D)
    (t : D ⟶ R) (n : R ⟶ T) (τ : D ⟶ T) (β : F₀ ⋙ G ≅ V ⋙ T)
    (e : F₀ ⋙ G ≅ F₁) (s : F₁ ≅ V ⋙ D) (Ψ : F₁ ≅ V ⋙ T)
    (hnat : Functor.whiskerRight δ G ≫ βr = θ ≫ Functor.whiskerLeft V t)
    (hδ : δ = 𝟙 F₀) (hθ : θ = (e ≪≫ s).hom)
    (ht : t ≫ n = τ) (hβ : β.hom = βr ≫ Functor.whiskerLeft V n)
    (hΨ : Ψ.hom = s.hom ≫ Functor.whiskerLeft V τ) :
    β = e ≪≫ Ψ := by
  apply Iso.ext
  have hr : βr = θ ≫ Functor.whiskerLeft V t := by
    simpa only [hδ, Functor.whiskerRight_id', Category.id_comp] using hnat
  rw [hβ, hr, Category.assoc, ← Functor.whiskerLeft_comp, ht, hθ, Iso.trans_hom,
    Iso.trans_hom, hΨ, Category.assoc]

universe u wX wS₀ wS₁ wM wX' wR wD
variable {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (C : Hom.DenseCompactification f) (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  (hS₀ : HasDerivedCategory.{wS₀} (ModuleSheaf S Λ))
  [hS₁ : HasDerivedCategory.{wS₁} (ModuleSheaf S Λ)]
  [hM : HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [hX' : HasDerivedCategory.{wX'} (ModuleSheaf (pullback (𝟙 S) f) Λ)]
  [hR : HasDerivedCategory.{wR} (ModuleSheaf (pullback (𝟙 S) C.p) Λ)]
  [hD : HasDerivedCategory.{wD}
    (ModuleSheaf (Hom.DenseCompactification.baseChangeObj (𝟙 S) C).Xbar Λ)]
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The local derived-category model on `ModuleSheaf (C.toCompactification.baseChange (𝟙 S)).Xbar
Λ`. -/
local instance normalizedBaseIdentityRaw :
    HasDerivedCategory.{wR}
      (ModuleSheaf (C.toCompactification.baseChange (𝟙 S)).Xbar Λ) := hR
/-- The local derived-category model on `ModuleSheaf
((Hom.DenseCompactification.identitySourceTransport f).obj C).Xbar Λ`. -/
local instance normalizedBaseIdentityTransport :
    HasDerivedCategory.{wM}
      (ModuleSheaf ((Hom.DenseCompactification.identitySourceTransport f).obj C).Xbar Λ) := hM
/-- The local derived-category model on `ModuleSheaf (Hom.Compactification.densify
(C.toCompactification.baseChange (𝟙 S))).Xbar Λ`. -/
local instance normalizedBaseIdentityDense :
    HasDerivedCategory.{wD}
      (ModuleSheaf (Hom.Compactification.densify
        (C.toCompactification.baseChange (𝟙 S))).Xbar Λ) := hD

/-- The actual normalized exchange with both base endpoints specified independently. -/
abbrev moduleUnboundedNormalizedBaseIdentityModelIso :=
  @moduleUnboundedNormalizedCompactificationBaseChangeIso X S S f _ C (𝟙 S)
    Λ _ hX hS₀ hM hX' hS₁ hR hD N hN hΛ

/-- The original identity base-change isomorphism factors through localization
transport and the independently defined original target-base source comparison. -/
theorem moduleUnboundedNormalizedBaseIdentityModelIso_eq :
    moduleUnboundedNormalizedBaseIdentityModelIso C Λ hS₀ N hN hΛ =
      moduleUnboundedRawCompactificationBaseIdentityIso C.toCompactification
        Λ hX hS₀ hS₁ hM ≪≫ moduleUnboundedIdentitySourceModelIso C Λ N hN hΛ := by
  apply normalize_base_identity
    (@moduleUnboundedRawCompactificationTransition X S f C.toCompactification
      C.toCompactification (𝟙 C.Xbar)
      (Hom.DenseCompactification.isPullback_open (𝟙 C)) (Category.id_comp C.p)
      Λ _ hX hS₀ hM hM)
    (moduleUnboundedRawBaseIdentityModelIso C Λ hX hS₀ hS₁ hM hX' hR N hN hΛ).hom
    (moduleUnboundedBaseModelSourceExchange (Hom.DenseCompactification.identitySourceIso f)
      C.j C.p Λ hX hX' hM hS₀ hS₁)
    (moduleUnboundedIdentityRawProjectionTransition C Λ)
    (moduleUnboundedCompactificationDensificationMap (C.toCompactification.baseChange (𝟙 S)) Λ)
    (moduleUnboundedIdentityComparisonTransition C Λ)
    (moduleUnboundedNormalizedBaseIdentityModelIso C Λ hS₀ N hN hΛ)
    (moduleUnboundedRawCompactificationBaseIdentityIso C.toCompactification
      Λ hX hS₀ hS₁ hM)
    (moduleUnboundedRawCompactificationSourceIso (Hom.DenseCompactification.identitySourceIso f) Λ
      (pullback.fst (𝟙 S) f) (Hom.DenseCompactification.identitySourceIso_hom_f f)
      C.toCompactification)
    (moduleUnboundedIdentitySourceModelIso C Λ N hN hΛ)
  · exact moduleUnboundedRawBaseIdentityModel_naturality C Λ hX hS₀ hS₁ hM hX' hR N hN hΛ
  · exact @moduleUnboundedRawDenseIdentityTransition X S f _ C Λ _ hX hS₀ hM
  · exact regroup_base_identity _ _ _ _ _
      (moduleUnboundedBaseModelSourceExchange_eq
        (Hom.DenseCompactification.identitySourceIso f) C.j C.p Λ hX hX' hM hS₀ hS₁)
  · exact moduleUnboundedIdentityNormalizationTransition C Λ
  · rfl
  · rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
