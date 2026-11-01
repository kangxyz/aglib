/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.NormalizedExchangePasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.RawBaseChangeIterationPasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.NormalizedBaseChangeIterationComparison

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

/-- Derived-category instance on module sheaves over `(pullback b C.p)`, using the instance on
`(C.toCompactification.baseChange b).Xbar`.
-/
local instance normalizedIterationFirstRawNativeModel :
    HasDerivedCategory.{wR₁} (ModuleSheaf (pullback b C.p) Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR₁}
    (ModuleSheaf (C.toCompactification.baseChange b).Xbar Λ))
/-- Derived-category instance on module sheaves over `(pullback c (C.toCompactification.baseChange
b).p)`, using the instance on `((C.toCompactification.baseChange b).baseChange c).Xbar`.
-/
local instance normalizedIterationSecondRawNativeModel :
    HasDerivedCategory.{wR₂}
      (ModuleSheaf (pullback c (C.toCompactification.baseChange b).p) Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR₂}
    (ModuleSheaf ((C.toCompactification.baseChange b).baseChange c).Xbar Λ))
/-- Derived-category instance on module sheaves over `(pullback c ((baseChange b).obj C).p)`, using
the instance on `(((baseChange b).obj C).toCompactification.baseChange c).Xbar`.
-/
local instance normalizedIterationSecondNormalizedRawNativeModel :
    HasDerivedCategory.{wRN} (ModuleSheaf (pullback c ((baseChange b).obj C).p) Λ) :=
  inferInstanceAs (HasDerivedCategory.{wRN}
    (ModuleSheaf (((baseChange b).obj C).toCompactification.baseChange c).Xbar Λ))

/-- Derived-category instance on module sheaves over `(baseChangeObj b C).Xbar`, using the instance
on `((baseChange b).obj C).Xbar`.
-/
local instance normalizedIterationFirstDenseModel :
    HasDerivedCategory.{wN₁} (ModuleSheaf (baseChangeObj b C).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN₁} (ModuleSheaf ((baseChange b).obj C).Xbar Λ))
/-- Derived-category instance on module sheaves over `(Hom.Compactification.densify
(C.toCompactification.baseChange b)).Xbar`, using the instance on `((baseChange b).obj C).Xbar`.
-/
local instance normalizedIterationFirstDensificationModel :
    HasDerivedCategory.{wN₁}
      (ModuleSheaf (Hom.Compactification.densify (C.toCompactification.baseChange b)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN₁} (ModuleSheaf ((baseChange b).obj C).Xbar Λ))
/-- Derived-category instance on module sheaves over `(baseChangeObj c ((baseChange b).obj
C)).Xbar`, using the instance on `((baseChange c).obj ((baseChange b).obj C)).Xbar`.
-/
local instance normalizedIterationSecondDenseModel :
    HasDerivedCategory.{wN₂} (ModuleSheaf (baseChangeObj c ((baseChange b).obj C)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN₂}
    (ModuleSheaf ((baseChange c).obj ((baseChange b).obj C)).Xbar Λ))
/-- Derived-category instance on module sheaves over `(Hom.Compactification.densify (((baseChange
b).obj C).toCompactification.baseChange c)).Xbar`, using the instance on `((baseChange c).obj
((baseChange b).obj C)).Xbar`.
-/
local instance normalizedIterationSecondDensificationModel :
    HasDerivedCategory.{wN₂} (ModuleSheaf (Hom.Compactification.densify
      (((baseChange b).obj C).toCompactification.baseChange c)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN₂}
    (ModuleSheaf ((baseChange c).obj ((baseChange b).obj C)).Xbar Λ))

/-- The actual composite raw exchange followed by both original normalization
steps, with the literal iterated source and the native composite inverse image. -/
def moduleNormalizedIterationCompositeMap :
    moduleRawCompactificationFunctor C.toCompactification Λ ⋙
        moduleDerivedInverseImage Λ (c ≫ b) ⟶
      moduleDerivedInverseImageTorsion
          (pullback.snd c (pullback.fst b f) ≫ pullback.snd b f) Λ ⋙
        moduleRawCompactificationFunctor
          ((baseChange c).obj ((baseChange b).obj C)).toCompactification Λ :=
  moduleRawIterationCompositeMap C.toCompactification b c Λ ≫
    Functor.whiskerLeft (moduleDerivedInverseImageTorsion
      (pullback.snd c (pullback.fst b f) ≫ pullback.snd b f) Λ)
      (moduleIterationFinalNormalizationMap b c C Λ)

/-- The two original normalized steps equal the original raw composite route
with its actual normalizations. No source-associator comparison is assumed. -/
theorem moduleNormalizedBaseChangeIteration_pasting :
    ∀ K, ActualHorizontalMateEquation
      (moduleNormalizedCompactificationBaseChangeIso C b Λ).hom
      (moduleNormalizedCompactificationBaseChangeIso ((baseChange b).obj C) c Λ).hom
      (moduleNormalizedIterationCompositeMap b c C Λ)
      (moduleDerivedInverseImageCompIso Λ b c).hom
      (moduleDerivedInverseImageTorsionCompIso Λ (pullback.snd b f)
        (pullback.snd c (pullback.fst b f))).hom K :=
  normalizedExchange_pasting
    (moduleRawCompactificationBaseChangeIso C.toCompactification b Λ).hom
    (moduleRawCompactificationBaseChangeIso (C.toCompactification.baseChange b) c Λ).hom
    (moduleRawIterationCompositeMap C.toCompactification b c Λ)
    (moduleDerivedInverseImageCompIso Λ b c).hom
    (moduleDerivedInverseImageTorsionCompIso Λ (pullback.snd b f)
      (pullback.snd c (pullback.fst b f))).hom
    (moduleCompactificationDensificationMap (C.toCompactification.baseChange b) Λ)
    (moduleIterationFinalNormalizationMap b c C Λ)
    (moduleNormalizedCompactificationBaseChangeIso C b Λ).hom
    (moduleNormalizedCompactificationBaseChangeIso ((baseChange b).obj C) c Λ).hom
    (moduleNormalizedIterationCompositeMap b c C Λ)
    (moduleRawBaseChangeIteration_pasting C.toCompactification b c Λ)
    (moduleNormalizedBaseChangeIteration_intermediate b c C Λ)
    (moduleNormalizedCompactificationBaseChangeIso_hom C b Λ) rfl

end AlgebraicGeometry.Scheme.EtaleCohomology
