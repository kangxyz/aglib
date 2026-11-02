/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.RawToDirectImageBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.NormalizedBaseChange

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
local instance : HasDerivedCategory.{wR}
    (ModuleSheaf (C.toCompactification.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ))
/-- The local derived-category model on `ModuleSheaf (Hom.Compactification.densify
(C.toCompactification.baseChange b)).Xbar Λ`. -/
local instance : HasDerivedCategory.{wN}
    (ModuleSheaf (Hom.Compactification.densify (C.toCompactification.baseChange b)).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wN}
    (ModuleSheaf (Hom.DenseCompactification.baseChangeObj b C).Xbar Λ))

/-- The original raw exchange followed by original densification still preserves b. -/
theorem moduleNormalizedCompactificationBaseChangeIso_toDirectImage :
    ExchangeToTargetEquation (moduleRawCompactificationToDirectImage C.toCompactification Λ)
      (moduleRawCompactificationToDirectImage
        (Hom.DenseCompactification.baseChangeObj b C).toCompactification Λ)
      (moduleNormalizedCompactificationBaseChangeIso C b Λ).hom
      (Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        (moduleDerivedBaseChangeMap Λ f (pullback.fst b f) b (pullback.snd b f)
          pullback.condition)) :=
  exchangeToTarget_postcompose
    (moduleRawCompactificationToDirectImage C.toCompactification Λ)
    (moduleRawCompactificationToDirectImage (C.toCompactification.baseChange b) Λ)
    (moduleRawCompactificationToDirectImage
      (Hom.DenseCompactification.baseChangeObj b C).toCompactification Λ)
    (moduleCompactificationDensificationMap (C.toCompactification.baseChange b) Λ)
    (moduleRawCompactificationBaseChangeIso C.toCompactification b Λ).hom
    (Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
      (moduleDerivedBaseChangeMap Λ f (pullback.fst b f) b (pullback.snd b f)
        pullback.condition))
    (moduleRawCompactificationToDirectImage_densification (C.toCompactification.baseChange b) Λ)
    (moduleRawCompactificationBaseChangeIso_toDirectImage C.toCompactification b Λ)
end AlgebraicGeometry.Scheme.EtaleCohomology
