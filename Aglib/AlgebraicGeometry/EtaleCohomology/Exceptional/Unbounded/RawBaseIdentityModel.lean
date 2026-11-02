/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseModelSourceExchange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawIdentityBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.IdentitySourceModel

/-! # Actual identity-pullback normalization with independent base models -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS₀ wS₁ wM wX' wR
variable {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (C : Hom.DenseCompactification f) (Λ : Type (u + 1)) [Ring Λ]
  (hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ))
  (hS₀ : HasDerivedCategory.{wS₀} (ModuleSheaf S Λ))
  (hS₁ : HasDerivedCategory.{wS₁} (ModuleSheaf S Λ))
  (hM : HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))
  (hX' : HasDerivedCategory.{wX'} (ModuleSheaf (pullback (𝟙 S) f) Λ))
  (hR : HasDerivedCategory.{wR} (ModuleSheaf (pullback (𝟙 S) C.p) Λ))
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- Literal original raw identity exchange; its base endpoints are kept explicit. -/
abbrev moduleUnboundedRawBaseIdentityModelIso :=
  @moduleUnboundedRawCompactificationBaseChangeIso X S S f C.toCompactification (𝟙 S)
    Λ _ hX hS₀ hM hX' hR hS₁ N hN hΛ

omit hX hS₀ N hN hΛ in
/-- The unchanged original projection transition, computed in the target base model. -/
abbrev moduleUnboundedRawBaseIdentityProjection :=
  @moduleUnboundedIdentityRawProjectionTransition X S f C Λ _ hS₁ hM hX' hR

include N hN hΛ in
/-- The original common-open refinement cube compares the raw identity pullback
with the source-only exchange, without identifying the two base models. -/
theorem moduleUnboundedRawBaseIdentityModel_naturality :
    Functor.whiskerRight
        (@moduleUnboundedRawCompactificationTransition X S f C.toCompactification
          C.toCompactification (𝟙 C.Xbar)
          (Hom.DenseCompactification.isPullback_open (𝟙 C)) (Category.id_comp C.p)
          Λ _ hX hS₀ hM hM)
        (@moduleUnboundedDerivedInverseImage Λ _ S S (𝟙 S) hS₀ hS₁) ≫
      (moduleUnboundedRawBaseIdentityModelIso C Λ hX hS₀ hS₁ hM hX' hR N hN hΛ).hom =
    moduleUnboundedBaseModelSourceExchange (Hom.DenseCompactification.identitySourceIso f)
        C.j C.p Λ hX hX' hM hS₀ hS₁ ≫
      Functor.whiskerLeft
        (@moduleUnboundedDerivedInverseImage Λ _ X (pullback (𝟙 S) f)
          (pullback.snd (𝟙 S) f) hX hX')
        (moduleUnboundedRawBaseIdentityProjection C Λ hS₁ hM hX' hR) := by
  exact @moduleUnboundedCompactifiedBaseChangeMap_refinement_naturality
    X C.Xbar C.Xbar (pullback (𝟙 S) f) (pullback (𝟙 S) C.p) C.Xbar
    C.j C.j (𝟙 C.Xbar) (Hom.DenseCompactification.isPullback_open (𝟙 C))
    (C.toCompactification.baseChange (𝟙 S)).j
    ((Hom.DenseCompactification.identitySourceTransport f).obj C).j
    (pullback.snd (𝟙 S) C.p) (Hom.DenseCompactification.isPullback_identityRawProjection_open C)
    (pullback.snd (𝟙 S) f) (pullback.snd (𝟙 S) C.p) (𝟙 C.Xbar)
    C.toCompactification.isOpenImmersion_j C.toCompactification.isOpenImmersion_j
    (C.toCompactification.baseChange (𝟙 S)).isOpenImmersion_j
    (Hom.Compactification.isOpenImmersion_j
      ((Hom.DenseCompactification.identitySourceTransport f).obj C).toCompactification)
    (isPullback_rawCompactificationOpen C.toCompactification (𝟙 S))
    (isPullback_sourceIsoOpen (Hom.DenseCompactification.identitySourceIso f) C.j)
    (Hom.DenseCompactification.isPullback_identityRawProjection C) Λ _
    hX hM hM hX' hR hM S S hS₀ hS₁
    C.p C.p (Category.id_comp C.p) (pullback.fst (𝟙 S) C.p) C.p
    (Hom.DenseCompactification.identityRawProjection_p C) (𝟙 S)
    (IsPullback.of_hasPullback (𝟙 S) C.p).flip (isPullback_sourceIsoProperIdentity C.p)

end AlgebraicGeometry.Scheme.EtaleCohomology
