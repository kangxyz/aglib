/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChangeIdentityTransition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawSourceIsoExchange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawBaseChangeNaturality

/-! # Original raw identity exchange compared with actual source transport -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS wM wX' wR
variable {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (C : Hom.DenseCompactification f) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf (pullback (𝟙 S) f) Λ)]
  [HasDerivedCategory.{wR} (ModuleSheaf (pullback (𝟙 S) C.p) Λ)]

local instance unboundedRawIdentityModel : HasDerivedCategory.{wR}
    (ModuleSheaf (C.toCompactification.baseChange (𝟙 S)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR} (ModuleSheaf (pullback (𝟙 S) C.p) Λ))
local instance unboundedRawIdentityTransportModel : HasDerivedCategory.{wM}
    (ModuleSheaf ((Hom.DenseCompactification.identitySourceTransport f).obj C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))

/-- The original raw transition along the actual identity-pullback projection. -/
def moduleUnboundedIdentityRawProjectionTransition :=
  moduleUnboundedRawCompactificationTransition
    (C.toCompactification.baseChange (𝟙 S))
    ((Hom.DenseCompactification.identitySourceTransport f).obj C).toCompactification
    (pullback.snd (𝟙 S) C.p)
    (Hom.DenseCompactification.isPullback_identityRawProjection_open C)
    (Hom.DenseCompactification.identityRawProjection_p C) Λ

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The original refinement/base-change square compares the raw identity
pullback with the source-transported original model. -/
theorem moduleUnboundedRawIdentityBaseChange_naturality :
    Functor.whiskerRight
      (moduleUnboundedRawCompactificationTransition C.toCompactification C.toCompactification
        (𝟙 C.Xbar) (Hom.DenseCompactification.isPullback_open (𝟙 C))
        (Category.id_comp C.p) Λ)
      (moduleUnboundedDerivedInverseImage Λ (𝟙 S)) ≫
      (moduleUnboundedRawCompactificationBaseChangeIso C.toCompactification (𝟙 S) Λ N hN hΛ).hom =
    moduleUnboundedRawSourceIsoBaseChangeMap (Hom.DenseCompactification.identitySourceIso f)
        (pullback.fst (𝟙 S) f) (Hom.DenseCompactification.identitySourceIso_hom_f f)
        C.toCompactification Λ ≫
      Functor.whiskerLeft (moduleUnboundedDerivedInverseImage Λ (pullback.snd (𝟙 S) f))
        (moduleUnboundedIdentityRawProjectionTransition C Λ) := by
  have hc := moduleUnboundedCompactifiedBaseChangeMap_refinement_naturality
    C.j C.j (𝟙 C.Xbar) (Hom.DenseCompactification.isPullback_open (𝟙 C))
    (C.toCompactification.baseChange (𝟙 S)).j
    ((Hom.DenseCompactification.identitySourceTransport f).obj C).j
    (pullback.snd (𝟙 S) C.p)
    (Hom.DenseCompactification.isPullback_identityRawProjection_open C)
    (pullback.snd (𝟙 S) f) (pullback.snd (𝟙 S) C.p) (𝟙 C.Xbar)
    (isPullback_rawCompactificationOpen C.toCompactification (𝟙 S))
    (isPullback_sourceIsoOpen (Hom.DenseCompactification.identitySourceIso f) C.j)
    (Hom.DenseCompactification.isPullback_identityRawProjection C) Λ
    C.p C.p (Category.id_comp C.p)
    (pullback.fst (𝟙 S) C.p) C.p
    (Hom.DenseCompactification.identityRawProjection_p C) (𝟙 S)
    (IsPullback.of_hasPullback (𝟙 S) C.p).flip
    (isPullback_sourceIsoProperIdentity C.p)
  exact hc

end AlgebraicGeometry.Scheme.EtaleCohomology
