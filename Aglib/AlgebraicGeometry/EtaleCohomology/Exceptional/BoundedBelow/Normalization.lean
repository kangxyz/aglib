/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.DirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.Densification
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Derived.Normalization
public import Aglib.AlgebraicGeometry.Compactification.Refinements.CompositionUnits

/-! # Proper and open normalization of the original exceptional direct image

Proper normalization uses the literal dense factorization with identity open map.
Open normalization uses a raw factorization and its original closed densification;
it does not assert schematic density of an arbitrary open immersion. Every
intermediate derived model remains independent of the native endpoint models.
-/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM wR

/-- The literal raw compactification of an open immersion; no density is required. -/
def moduleOpenRawCompactification {X S : Scheme.{u}} (f : X ⟶ S)
    [IsOpenImmersion f] : Hom.Compactification f where
  Xbar := S
  j := f
  p := 𝟙 S
  isOpenImmersion_j := inferInstance
  isProper_p := inferInstance
  fac := Category.comp_id f

instance {X S : Scheme.{u}} (f : X ⟶ S) [IsOpenImmersion f] [QuasiCompact f] :
    QuasiCompact (moduleOpenRawCompactification f).j :=
  inferInstanceAs (QuasiCompact f)

variable {X S : Scheme.{u}} (f : X ⟶ S) (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [middleModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- Normalization of the actual proper model to the same native direct image. -/
def moduleProperCompactificationNormalizationIso [IsProper f] :
    moduleCompactificationFunctor f Λ (Hom.DenseCompactification.ofProper f) ≅
      (moduleTorsionCohomologyPlus X Λ).ι ⋙ moduleDerivedDirectImage Λ f :=
  Functor.isoWhiskerLeft _ (moduleDerivedProperNormalizationIso f Λ hX hS
    (middleModels (Hom.DenseCompactification.ofProper f)))

section Chosen
variable [CompactSpace S] [QuasiSeparatedSpace S]

/-- Proper exceptional image is its original native direct image, by the original
chosen comparison and the literal proper-factorization contraction. -/
def moduleExceptionalProperNormalizationIso [IsProper f] :
    moduleExceptionalDirectImagePlus f Λ ≅
      (moduleTorsionCohomologyPlus X Λ).ι ⋙ moduleDerivedDirectImage Λ f :=
  moduleExceptionalDirectImagePlusIso f Λ (Hom.DenseCompactification.ofProper f) ≪≫
    moduleProperCompactificationNormalizationIso f Λ

/-- The proper normalization retains the actual chosen-comparison formula. -/
theorem moduleExceptionalProperNormalizationIso_hom [IsProper f] :
    (moduleExceptionalProperNormalizationIso f Λ).hom =
      (moduleExceptionalDirectImagePlusIso f Λ (Hom.DenseCompactification.ofProper f)).hom ≫
        (moduleProperCompactificationNormalizationIso f Λ).hom := rfl

variable [IsOpenImmersion f] [QuasiCompact f]
  (rawModel : HasDerivedCategory.{wR} (ModuleSheaf S Λ))

/-- Open normalization passes backwards through the original densification unit
before contracting the actual raw factorization. The raw model is independent. -/
def moduleExceptionalOpenNormalizationIso :
    letI := hS
    moduleExceptionalDirectImagePlus f Λ ≅
      (moduleTorsionCohomologyPlus X Λ).ι ⋙ moduleDerivedLowerShriek f Λ := by
  letI := hS
  exact moduleExceptionalDirectImagePlusIso f Λ
      (Hom.Compactification.densify (moduleOpenRawCompactification f)) ≪≫
    (@moduleCompactificationDensificationIso X S f (moduleOpenRawCompactification f)
      inferInstance Λ _ hX hS rawModel
      (middleModels (Hom.Compactification.densify (moduleOpenRawCompactification f)))).symm ≪≫
    Functor.isoWhiskerLeft _ (moduleDerivedOpenNormalizationIso f Λ hX hS rawModel)

/-- The open normalization retains the original comparison, densification inverse,
and raw-factorization contraction, rather than an unspecified isomorphism. -/
theorem moduleExceptionalOpenNormalizationIso_hom :
    letI := hS
    (moduleExceptionalOpenNormalizationIso f Λ rawModel).hom =
      (moduleExceptionalDirectImagePlusIso f Λ
        (Hom.Compactification.densify (moduleOpenRawCompactification f))).hom ≫
      (@moduleCompactificationDensificationIso X S f (moduleOpenRawCompactification f)
        inferInstance Λ _ hX hS rawModel
        (middleModels (Hom.Compactification.densify (moduleOpenRawCompactification f)))).inv ≫
      Functor.whiskerLeft _ (moduleDerivedOpenNormalizationIso f Λ hX hS rawModel).hom := by
  let := hS
  rfl

end Chosen
end AlgebraicGeometry.Scheme.EtaleCohomology
