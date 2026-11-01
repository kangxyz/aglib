/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenNormalization
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenToDirectImageComposition
public import Aglib.CategoryTheory.NatTrans.TargetComparisonTransport

/-! # Open normalization preserves the same original unbounded canonical comparison -/
@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wT wM wR
section Composite
variable (Λ : Type (u + 1)) [Ring Λ] {X S T : Scheme.{u}}
  (f : S ⟶ X) (g : T ⟶ S) [IsIso f] [IsOpenImmersion g]
  [hTarget : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hMiddle : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [hSource : HasDerivedCategory.{wT} (ModuleSheaf T Λ)]

/-- Original triple composition proves the actual postcomposition normalization square. -/
theorem moduleUnboundedOpenPostcomposeNormalization_toDirectImage :
    TargetComparisonEquation (moduleUnboundedOpenPostcomposeNormalizationIso Λ f g).hom
      (moduleUnboundedLowerShriekToDirectImage Λ (g ≫ f))
      (Functor.whiskerRight (moduleUnboundedLowerShriekToDirectImage Λ g)
          (moduleUnboundedDerivedDirectImage Λ f) ≫
        (moduleUnboundedDerivedDirectImageCompIso Λ f g).inv) := by
  let := moduleUnboundedLowerShriekToDirectImage_isIso_of_isIso Λ f
  exact openPostcomposeNormalization_toTarget
    (moduleUnboundedLowerShriekToDirectImage Λ (g ≫ f))
    (moduleUnboundedLowerShriekToDirectImage Λ g)
    (asIso (moduleUnboundedLowerShriekToDirectImage Λ f))
    (moduleUnboundedDerivedLowerShriekCompIso Λ f g)
    (moduleUnboundedDerivedDirectImageCompIso Λ f g)
    (moduleUnboundedLowerShriekToDirectImage_comp Λ g f)

/-- The same comparison equation retains the literal geometric structural triangle. -/
theorem moduleUnboundedOpenPostcomposeOverNormalization_toDirectImage
    (k : T ⟶ X) [IsOpenImmersion k] (h : g ≫ f = k) :
    TargetComparisonEquation
      (moduleUnboundedOpenPostcomposeOverNormalizationIso Λ k f g h).hom
      (moduleUnboundedLowerShriekToDirectImage Λ k)
      (Functor.whiskerRight (moduleUnboundedLowerShriekToDirectImage Λ g)
          (moduleUnboundedDerivedDirectImage Λ f) ≫
        (moduleUnboundedDerivedDirectImageOverIso Λ k f g h).hom) := by
  subst k
  simpa only [moduleUnboundedOpenPostcomposeOverNormalizationIso,
    moduleUnboundedDerivedDirectImageOverIso, eqToIso_refl, Iso.trans_refl, Iso.symm_hom] using
    moduleUnboundedOpenPostcomposeNormalization_toDirectImage Λ f g
end Composite

variable {X S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]
  (f : X ⟶ S) [IsOpenImmersion f] [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [middleModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  (rawModel : HasDerivedCategory.{wR} (ModuleSheaf S Λ))
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The chosen open normalization intertwines the same canonical map, not an iso surrogate. -/
theorem moduleExceptionalUnboundedOpenNormalization_canonical :
    letI := hS
    TargetComparisonEquation
      (moduleExceptionalUnboundedOpenNormalizationIso f Λ rawModel N hN hΛ).hom
      (moduleUnboundedLowerShriekToDirectImage Λ f)
      (moduleExceptionalToDirectImageUnbounded f Λ) := by
  let := hS
  exact targetComparison_iso_trans
    (moduleExceptionalUnboundedRawComparisonIso (moduleOpenRawCompactification f) Λ N hN hΛ
      (hC := rawModel))
    (moduleUnboundedOpenRawNormalizationIso f Λ rawModel)
    (moduleExceptionalToDirectImageUnbounded f Λ)
    (@moduleUnboundedRawCompactificationToDirectImage X S f (moduleOpenRawCompactification f)
      Λ _ hX hS rawModel)
    (moduleUnboundedLowerShriekToDirectImage Λ f)
    (moduleExceptionalToDirectImageUnbounded_raw_model (hC := rawModel)
      (moduleOpenRawCompactification f) Λ N hN hΛ)
    (moduleUnboundedOpenPostcomposeOverNormalization_toDirectImage Λ (𝟙 S) f f
      (Category.comp_id f) (hTarget := hS) (hMiddle := rawModel) (hSource := hX))
end AlgebraicGeometry.Scheme.EtaleCohomology
