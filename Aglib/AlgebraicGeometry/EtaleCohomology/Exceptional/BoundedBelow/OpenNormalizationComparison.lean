/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.Normalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.RawComparisonToDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.IdentityTargetComposition
public import Aglib.CategoryTheory.NatTrans.TargetComparisonWhiskering

/-! # Open normalization preserves the same original canonical exceptional comparison

The actual raw-open factorization is retained, including its independent
ambient model and its original closed-densification comparison.
-/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM wR
variable {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
  (f : X ⟶ S) [IsOpenImmersion f] [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [middleModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  (rawModel : HasDerivedCategory.{wR} (ModuleSheaf S Λ))

/-- The chosen open normalization intertwines the same canonical maps,
without an iso premise on them. -/
theorem moduleExceptionalOpenNormalization_canonical :
    letI := hS
    TargetComparisonEquation (moduleExceptionalOpenNormalizationIso f Λ rawModel).hom
      (Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        (moduleDerivedLowerShriekToDirectImage Λ f))
      (moduleExceptionalToDirectImage f Λ) := by
  let := hS
  exact targetComparison_iso_trans_three
    (moduleExceptionalDirectImagePlusIso f Λ
      (Hom.Compactification.densify (moduleOpenRawCompactification f)))
    (@moduleCompactificationDensificationIso X S f (moduleOpenRawCompactification f)
      inferInstance Λ _ hX hS rawModel
      (middleModels (Hom.Compactification.densify (moduleOpenRawCompactification f)))).symm
    (Functor.isoWhiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
      (moduleDerivedOpenNormalizationIso f Λ hX hS rawModel))
    (moduleExceptionalToDirectImage f Λ)
    (@moduleRawCompactificationToDirectImage X S f (moduleOpenRawCompactification f)
      Λ _ hX hS rawModel)
    (Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
      (moduleDerivedLowerShriekToDirectImage Λ f))
    (moduleExceptionalToDirectImage_raw_model (hC := rawModel)
      (moduleOpenRawCompactification f) Λ)
    (targetComparison_whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
      (moduleDerivedOpenNormalizationIso f Λ hX hS rawModel).hom
      (moduleDerivedLowerShriekToDirectImage Λ f) _
      (moduleDerivedOpenNormalizationIso_toDirectImage Λ f hX rawModel hS))

end AlgebraicGeometry.Scheme.EtaleCohomology
