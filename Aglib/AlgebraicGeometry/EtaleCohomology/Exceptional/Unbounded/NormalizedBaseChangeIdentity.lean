/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.NormalizedIdentity
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawIdentityBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.NormalizedBaseChange

/-!
# Actual normalized identity base change in the supplied common models

The base and the transported original ambient retain their original derived
models. The raw and normalized pullback ambients and the literal pullback
source have independent models. Transport to independently chosen copies of
the same base or ambient category is a separate native-model comparison step.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS wM wX' wR wN
variable {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (C : Hom.DenseCompactification f) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf (pullback (𝟙 S) f) Λ)]
  [HasDerivedCategory.{wR} (ModuleSheaf (pullback (𝟙 S) C.p) Λ)]
  [HasDerivedCategory.{wN}
    (ModuleSheaf (Hom.DenseCompactification.baseChangeObj (𝟙 S) C).Xbar Λ)]

local instance unboundedNormalizedIdentityRawModel : HasDerivedCategory.{wR}
    (ModuleSheaf (C.toCompactification.baseChange (𝟙 S)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR} (ModuleSheaf (pullback (𝟙 S) C.p) Λ))
local instance unboundedNormalizedIdentityTransportModel : HasDerivedCategory.{wM}
    (ModuleSheaf ((Hom.DenseCompactification.identitySourceTransport f).obj C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ))
local instance unboundedNormalizedIdentityDenseModel : HasDerivedCategory.{wN}
    (ModuleSheaf (Hom.Compactification.densify (C.toCompactification.baseChange (𝟙 S))).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN}
    (ModuleSheaf (Hom.DenseCompactification.baseChangeObj (𝟙 S) C).Xbar Λ))

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- Normalized identity base change is the original source transport followed
by the transition of the actual dense identity comparison. -/
theorem moduleUnboundedNormalizedCompactificationBaseChangeIso_identity :
    NormalizedIdentityBaseChangeEquation
      (moduleUnboundedNormalizedCompactificationBaseChangeIso C (𝟙 S) Λ N hN hΛ).hom
      (moduleUnboundedDerivedInverseImageIdIso Λ S)
      (moduleUnboundedRawCompactificationSourceIso (Hom.DenseCompactification.identitySourceIso f) Λ
        (pullback.fst (𝟙 S) f) (Hom.DenseCompactification.identitySourceIso_hom_f f)
        C.toCompactification)
      (moduleUnboundedRawCompactificationTransition
        (Hom.DenseCompactification.baseChangeObj (𝟙 S) C).toCompactification
        ((Hom.DenseCompactification.identitySourceTransport f).obj C).toCompactification
        (Hom.DenseCompactification.baseChangeIdentityIso f C).hom.hom
        (Hom.DenseCompactification.isPullback_open
          (Hom.DenseCompactification.baseChangeIdentityIso f C).hom)
        (Hom.DenseCompactification.baseChangeIdentityIso f C).hom.base_fac Λ) :=
  normalizedIdentityBaseChangeEquation
    (moduleUnboundedRawCompactificationTransition C.toCompactification C.toCompactification
      (𝟙 C.Xbar) (Hom.DenseCompactification.isPullback_open (𝟙 C))
      (Category.id_comp C.p) Λ)
    (moduleUnboundedRawCompactificationBaseChangeIso C.toCompactification (𝟙 S) Λ N hN hΛ).hom
    (moduleUnboundedRawSourceIsoBaseChangeMap (Hom.DenseCompactification.identitySourceIso f)
      (pullback.fst (𝟙 S) f) (Hom.DenseCompactification.identitySourceIso_hom_f f)
      C.toCompactification Λ)
    (moduleUnboundedIdentityRawProjectionTransition C Λ)
    (moduleUnboundedCompactificationDensificationMap (C.toCompactification.baseChange (𝟙 S)) Λ)
    _ (moduleUnboundedNormalizedCompactificationBaseChangeIso C (𝟙 S) Λ N hN hΛ).hom
    (moduleUnboundedDerivedInverseImageIdIso Λ S) _
    (moduleUnboundedRawIdentityBaseChange_naturality C Λ N hN hΛ)
    (moduleUnboundedRawDenseIdentityTransition C Λ)
    (moduleUnboundedRawSourceIsoBaseChangeMap_identity
      (Hom.DenseCompactification.identitySourceIso f)
      (pullback.fst (𝟙 S) f) (Hom.DenseCompactification.identitySourceIso_hom_f f)
      C.toCompactification Λ)
    (moduleUnboundedIdentityNormalizationTransition C Λ)
    (moduleUnboundedNormalizedCompactificationBaseChangeIso_hom C (𝟙 S) Λ N hN hΛ)

end AlgebraicGeometry.Scheme.EtaleCohomology
