/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.NormalizedExchangePasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawBaseChangeIterationPasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.NormalizedBaseChangeIterationComparison

/-!
# Original normalized exchange pasting on the literal iterated source

The actual raw composite exchange is followed by the actual pulled first
normalization and second densification. The original raw pasting and the proved
intermediate normalization square identify this map with the two normalized
steps. Identifying it with a single normalized pullback transported along the
native source associator remains a separate original-map comparison.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients Hom.DenseCompactification

universe u wX wS wM wX₁ wT wR₁ wN₁ wX₂ wU wR₂ wRN wN₂

variable {X S T U : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (b : T ⟶ S) (c : U ⟶ T) (C : Hom.DenseCompactification f)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wX₁} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wR₁} (ModuleSheaf (C.toCompactification.baseChange b).Xbar Λ)]
  [HasDerivedCategory.{wN₁} (ModuleSheaf ((baseChange b).obj C).Xbar Λ)]
  [HasDerivedCategory.{wX₂} (ModuleSheaf (pullback c (pullback.fst b f)) Λ)]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wR₂}
    (ModuleSheaf ((C.toCompactification.baseChange b).baseChange c).Xbar Λ)]
  [HasDerivedCategory.{wRN}
    (ModuleSheaf (((baseChange b).obj C).toCompactification.baseChange c).Xbar Λ)]
  [HasDerivedCategory.{wN₂} (ModuleSheaf ((baseChange c).obj ((baseChange b).obj C)).Xbar Λ)]

local instance unboundedNormalizedIterationFirstRawNativeModel :
    HasDerivedCategory.{wR₁} (ModuleSheaf (pullback b C.p) Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR₁}
    (ModuleSheaf (C.toCompactification.baseChange b).Xbar Λ))
local instance unboundedNormalizedIterationSecondRawNativeModel :
    HasDerivedCategory.{wR₂}
      (ModuleSheaf (pullback c (C.toCompactification.baseChange b).p) Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR₂}
    (ModuleSheaf ((C.toCompactification.baseChange b).baseChange c).Xbar Λ))
local instance unboundedNormalizedIterationSecondNormalizedRawNativeModel :
    HasDerivedCategory.{wRN} (ModuleSheaf (pullback c ((baseChange b).obj C).p) Λ) :=
  inferInstanceAs (HasDerivedCategory.{wRN}
    (ModuleSheaf (((baseChange b).obj C).toCompactification.baseChange c).Xbar Λ))

local instance unboundedNormalizedIterationFirstDenseModel :
    HasDerivedCategory.{wN₁} (ModuleSheaf (baseChangeObj b C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN₁} (ModuleSheaf ((baseChange b).obj C).Xbar Λ))
local instance unboundedNormalizedIterationFirstDensificationModel :
    HasDerivedCategory.{wN₁}
      (ModuleSheaf (Hom.Compactification.densify (C.toCompactification.baseChange b)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN₁} (ModuleSheaf ((baseChange b).obj C).Xbar Λ))
local instance unboundedNormalizedIterationSecondDenseModel :
    HasDerivedCategory.{wN₂} (ModuleSheaf (baseChangeObj c ((baseChange b).obj C)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN₂}
    (ModuleSheaf ((baseChange c).obj ((baseChange b).obj C)).Xbar Λ))
local instance unboundedNormalizedIterationSecondDensificationModel :
    HasDerivedCategory.{wN₂} (ModuleSheaf (Hom.Compactification.densify
      (((baseChange b).obj C).toCompactification.baseChange c)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN₂}
    (ModuleSheaf ((baseChange c).obj ((baseChange b).obj C)).Xbar Λ))

/-- The actual composite raw exchange followed by both original normalization
steps, with the literal iterated source and the native composite inverse image. -/
def moduleUnboundedNormalizedIterationCompositeMap :
    moduleUnboundedRawCompactificationFunctor C.toCompactification Λ ⋙
        moduleUnboundedDerivedInverseImage Λ (c ≫ b) ⟶
      moduleUnboundedDerivedInverseImage Λ
          (pullback.snd c (pullback.fst b f) ≫ pullback.snd b f) ⋙
        moduleUnboundedRawCompactificationFunctor
          ((baseChange c).obj ((baseChange b).obj C)).toCompactification Λ :=
  moduleUnboundedRawIterationCompositeMap C.toCompactification b c Λ ≫
    Functor.whiskerLeft (moduleUnboundedDerivedInverseImage Λ
      (pullback.snd c (pullback.fst b f) ≫ pullback.snd b f))
      (moduleUnboundedIterationFinalNormalizationMap b c C Λ)

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The two original normalized steps equal the original raw composite route
with its actual normalizations. No source-associator comparison is assumed. -/
theorem moduleUnboundedNormalizedBaseChangeIteration_pasting :
    ∀ K, ActualHorizontalMateEquation
      (moduleUnboundedNormalizedCompactificationBaseChangeIso C b Λ N hN hΛ).hom
      (moduleUnboundedNormalizedCompactificationBaseChangeIso
          ((baseChange b).obj C) c Λ N hN hΛ).hom
      (moduleUnboundedNormalizedIterationCompositeMap b c C Λ)
      (moduleUnboundedDerivedInverseImageCompIso Λ b c).hom
      (moduleUnboundedDerivedInverseImageCompIso Λ (pullback.snd b f)
        (pullback.snd c (pullback.fst b f))).hom K :=
  normalizedExchange_pasting
    (moduleUnboundedRawCompactificationBaseChangeIso C.toCompactification b Λ N hN hΛ).hom
    (moduleUnboundedRawCompactificationBaseChangeIso
        (C.toCompactification.baseChange b) c Λ N hN hΛ).hom
    (moduleUnboundedRawIterationCompositeMap C.toCompactification b c Λ)
    (moduleUnboundedDerivedInverseImageCompIso Λ b c).hom
    (moduleUnboundedDerivedInverseImageCompIso Λ (pullback.snd b f)
      (pullback.snd c (pullback.fst b f))).hom
    (moduleUnboundedCompactificationDensificationMap (C.toCompactification.baseChange b) Λ)
    (moduleUnboundedIterationFinalNormalizationMap b c C Λ)
    (moduleUnboundedNormalizedCompactificationBaseChangeIso C b Λ N hN hΛ).hom
    (moduleUnboundedNormalizedCompactificationBaseChangeIso ((baseChange b).obj C) c Λ N hN hΛ).hom
    (moduleUnboundedNormalizedIterationCompositeMap b c C Λ)
    (moduleUnboundedRawBaseChangeIteration_pasting C.toCompactification b c Λ N hN hΛ)
    (moduleUnboundedNormalizedBaseChangeIteration_intermediate b c C Λ N hN hΛ)
    (moduleUnboundedNormalizedCompactificationBaseChangeIso_hom C b Λ N hN hΛ) rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
