/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenIsomorphism
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.LowerShriekComposition
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawComparisonToDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.Normalization
public import Aglib.CategoryTheory.Adjunction.OpenPostcomposeNormalization

/-! # Actual unbounded open normalization through independent raw and target models -/
@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wT wM wR

/-- Original contraction through an invertible second canonical comparison. -/
def moduleUnboundedOpenPostcomposeNormalizationIso (Λ : Type (u + 1)) [Ring Λ]
    {X S T : Scheme.{u}} (f : S ⟶ X) (g : T ⟶ S) [IsIso f] [IsOpenImmersion g]
    [hTarget : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [hMiddle : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [hSource : HasDerivedCategory.{wT} (ModuleSheaf T Λ)] :
    moduleUnboundedDerivedLowerShriek g Λ ⋙ moduleUnboundedDerivedDirectImage Λ f ≅
      moduleUnboundedDerivedLowerShriek (g ≫ f) Λ := by
  letI := moduleUnboundedLowerShriekToDirectImage_isIso_of_isIso Λ f
  exact openPostcomposeNormalizationIso (moduleUnboundedDerivedLowerShriekCompIso Λ f g)
    (asIso (moduleUnboundedLowerShriekToDirectImage Λ f))

/-- Contract an actual geometric structural triangle using its literal arrow equality. -/
def moduleUnboundedOpenPostcomposeOverNormalizationIso (Λ : Type (u + 1)) [Ring Λ]
    {X S T : Scheme.{u}} (k : T ⟶ X) (f : S ⟶ X) (g : T ⟶ S)
    [IsIso f] [IsOpenImmersion g] [IsOpenImmersion k] (h : g ≫ f = k)
    [hTarget : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
    [hMiddle : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
    [hSource : HasDerivedCategory.{wT} (ModuleSheaf T Λ)] :
    moduleUnboundedDerivedLowerShriek g Λ ⋙ moduleUnboundedDerivedDirectImage Λ f ≅
      moduleUnboundedDerivedLowerShriek k Λ := by
  subst k
  exact moduleUnboundedOpenPostcomposeNormalizationIso Λ f g

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsOpenImmersion f] [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  (rawModel : HasDerivedCategory.{wR} (ModuleSheaf S Λ))

/-- Literal raw open factorization, contracted without identifying the two target models. -/
def moduleUnboundedOpenRawNormalizationIso :
    letI := hS
    @moduleUnboundedRawCompactificationFunctor X S f (moduleOpenRawCompactification f)
      Λ _ hX hS rawModel ≅ moduleUnboundedDerivedLowerShriek f Λ := by
  letI := hS
  exact moduleUnboundedOpenPostcomposeOverNormalizationIso Λ f (𝟙 S) f (Category.comp_id f)
    (hTarget := hS) (hMiddle := rawModel) (hSource := hX)

variable [CompactSpace S] [QuasiSeparatedSpace S]
  [middleModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The chosen open normalization uses actual densification and its original raw contraction. -/
def moduleExceptionalUnboundedOpenNormalizationIso :
    letI := hS
    moduleExceptionalDirectImageUnbounded f Λ ≅ moduleUnboundedDerivedLowerShriek f Λ := by
  letI := hS
  exact moduleExceptionalUnboundedRawComparisonIso (moduleOpenRawCompactification f) Λ N hN hΛ
      (hC := rawModel) ≪≫
    moduleUnboundedOpenRawNormalizationIso f Λ rawModel
end AlgebraicGeometry.Scheme.EtaleCohomology
