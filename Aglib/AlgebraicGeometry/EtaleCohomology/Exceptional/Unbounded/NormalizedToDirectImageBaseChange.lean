/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawToDirectImageBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.NormalizedBaseChange

/-! # Actual schematic-image normalization preserves the same base-change square -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM wX' wT wR wN
variable {X S T : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (C : Hom.DenseCompactification f) (b : T ⟶ S)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ)]
  [HasDerivedCategory.{wN} (ModuleSheaf (Hom.DenseCompactification.baseChangeObj b C).Xbar Λ)]

/-- The local derived-category model on `ModuleSheaf (C.toCompactification.baseChange b).Xbar Λ`.
-/
local instance unboundedNormalizedToTargetRawModel : HasDerivedCategory.{wR}
    (ModuleSheaf (C.toCompactification.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ))
/-- The local derived-category model on `ModuleSheaf (Hom.Compactification.densify
(C.toCompactification.baseChange b)).Xbar Λ`. -/
local instance unboundedNormalizedToTargetDenseModel :
    HasDerivedCategory.{wN}
    (ModuleSheaf (Hom.Compactification.densify (C.toCompactification.baseChange b)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN}
    (ModuleSheaf (Hom.DenseCompactification.baseChangeObj b C).Xbar Λ))

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The original raw exchange followed by original densification still preserves b. -/
theorem moduleUnboundedNormalizedCompactificationBaseChangeIso_toDirectImage :
    ExchangeToTargetEquation
      (moduleUnboundedRawCompactificationToDirectImage C.toCompactification Λ)
      (moduleUnboundedRawCompactificationToDirectImage
        (Hom.DenseCompactification.baseChangeObj b C).toCompactification Λ)
      (moduleUnboundedNormalizedCompactificationBaseChangeIso C b Λ N hN hΛ).hom
      (moduleUnboundedDerivedBaseChangeMap Λ f (pullback.fst b f) b (pullback.snd b f)
        pullback.condition) :=
  exchangeToTarget_postcompose
    (moduleUnboundedRawCompactificationToDirectImage C.toCompactification Λ)
    (moduleUnboundedRawCompactificationToDirectImage (C.toCompactification.baseChange b) Λ)
    (moduleUnboundedRawCompactificationToDirectImage
      (Hom.DenseCompactification.baseChangeObj b C).toCompactification Λ)
    (moduleUnboundedCompactificationDensificationMap (C.toCompactification.baseChange b) Λ)
    (moduleUnboundedRawCompactificationBaseChangeIso C.toCompactification b Λ N hN hΛ).hom
    (moduleUnboundedDerivedBaseChangeMap Λ f (pullback.fst b f) b (pullback.snd b f)
      pullback.condition)
    (moduleUnboundedRawCompactificationToDirectImage_densification
      (C.toCompactification.baseChange b) Λ)
    (moduleUnboundedRawCompactificationBaseChangeIso_toDirectImage C.toCompactification b Λ N hN hΛ)
end AlgebraicGeometry.Scheme.EtaleCohomology
