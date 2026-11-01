/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.Normalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.ToDirectImageNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.ProperNormalizationComparison
public import Aglib.CategoryTheory.NatTrans.CanonicalMapNormalization

/-! # Proper normalization is the same original canonical exceptional-to-ordinary map -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM
variable {X S : Scheme.{u}} (f : X ⟶ S) [IsProper f]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [middleModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- On the literal proper compactification, normalization has the original canonical hom. -/
theorem moduleProperCompactificationNormalization_canonical :
    CanonicalMapNormalizationEquation
      (moduleCompactificationToDirectImage f Λ (Hom.DenseCompactification.ofProper f))
      (moduleProperCompactificationNormalizationIso f Λ) :=
  canonicalMapNormalization_whisker_of_iso_eq (moduleTorsionCohomologyPlus X Λ).ι
    (moduleDerivedLowerShriekToDirectImage Λ (Hom.DenseCompactification.ofProper f).j)
    (moduleDerivedIdentityOuterIso Λ X hX
      (middleModels (Hom.DenseCompactification.ofProper f)))
    (moduleDerivedProperDirectImageNormalizationIso f Λ hX hS
      (middleModels (Hom.DenseCompactification.ofProper f)))
    (moduleDerivedDirectImageOverIso Λ f (Hom.DenseCompactification.ofProper f).p
      (Hom.DenseCompactification.ofProper f).j (Hom.DenseCompactification.ofProper f).fac)
    (moduleDerivedProperNormalizationIso f Λ hX hS
      (middleModels (Hom.DenseCompactification.ofProper f)))
    (moduleDerivedLowerShriekToDirectImage_identity_models Λ X hX
      (middleModels (Hom.DenseCompactification.ofProper f)))
    (moduleDerivedProperDirectImageNormalizationIso_eq_over f Λ hX hS
      (middleModels (Hom.DenseCompactification.ofProper f)))
    (moduleDerivedProperNormalizationIso_outer f Λ hX hS
      (middleModels (Hom.DenseCompactification.ofProper f)))

variable [CompactSpace S] [QuasiSeparatedSpace S]

/-- Proper normalization of the chosen exceptional functor is its same canonical map to `Rf*`. -/
theorem moduleExceptionalProperNormalization_canonical :
    CanonicalMapNormalizationEquation (moduleExceptionalToDirectImage f Λ)
      (moduleExceptionalProperNormalizationIso f Λ) :=
  canonicalMapNormalization_comparison (moduleExceptionalToDirectImage f Λ)
    (moduleCompactificationToDirectImage f Λ (Hom.DenseCompactification.ofProper f))
    (moduleExceptionalDirectImagePlusIso f Λ (Hom.DenseCompactification.ofProper f))
    (moduleProperCompactificationNormalizationIso f Λ)
    (moduleExceptionalToDirectImage_model f Λ (Hom.DenseCompactification.ofProper f))
    (moduleProperCompactificationNormalization_canonical f Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
