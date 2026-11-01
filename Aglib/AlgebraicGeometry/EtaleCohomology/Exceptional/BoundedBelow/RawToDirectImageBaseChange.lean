/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Compactification.ToDirectImageBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.RawToDirectImage
public import Aglib.CategoryTheory.NatTrans.CompositeExchangeToTargetRestriction

/-! # Actual raw base change on torsion inputs retains the same canonical comparison -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM wX' wT wR
variable {X S T : Scheme.{u}} {f : X ⟶ S}
  (C : Hom.Compactification f) (b : T ⟶ S)
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ)]

/-- The local derived-category model on `ModuleSheaf (C.baseChange b).Xbar Λ`. -/
local instance rawToDirectImageBaseChangeModel :
    HasDerivedCategory.{wR} (ModuleSheaf (C.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ))

/-- Literal raw pullback base change, not a substituted isomorphism, preserves b. -/
theorem moduleRawCompactificationBaseChangeIso_toDirectImage :
    ExchangeToTargetEquation (moduleRawCompactificationToDirectImage C Λ)
      (moduleRawCompactificationToDirectImage (C.baseChange b) Λ)
      (moduleRawCompactificationBaseChangeIso C b Λ).hom
      (Functor.whiskerLeft (moduleTorsionCohomologyPlus X Λ).ι
        (moduleDerivedBaseChangeMap Λ f (pullback.fst b f) b (pullback.snd b f)
          pullback.condition)) :=
  compositeExchange_toTarget_restrict
    (moduleDerivedLowerShriekToDirectImage Λ C.j)
    (moduleDerivedLowerShriekToDirectImage Λ (C.baseChange b).j)
    (moduleDerivedDirectImageOverIso Λ f C.p C.j C.fac)
    (moduleDerivedDirectImageOverIso Λ (pullback.fst b f) (pullback.fst b C.p)
      (C.baseChange b).j (C.baseChange b).fac)
    (moduleDerivedBaseChangeMap Λ C.p (pullback.fst b C.p) b (pullback.snd b C.p)
      (IsPullback.of_hasPullback b C.p).flip.w.symm)
    (moduleDerivedLowerShriekCartesianBaseChangeIso (pullback.snd b f) (C.baseChange b).j
      C.j (pullback.snd b C.p) (isPullback_rawCompactificationOpen C b) Λ)
    (moduleDerivedBaseChangeMap Λ f (pullback.fst b f) b (pullback.snd b f) pullback.condition)
    (moduleTorsionCohomologyPlus X Λ) (moduleTorsionCohomologyPlus (pullback b f) Λ)
    (fun K => ((moduleDerivedInverseImageTorsion (pullback.snd b f) Λ).obj K).property)
    (compactifiedExchange_isIsoOn C.j C.p (C.baseChange b).j (pullback.fst b C.p)
      (pullback.snd b f) (pullback.snd b C.p) b
      (isPullback_rawCompactificationOpen C b) (IsPullback.of_hasPullback b C.p).flip Λ)
    (moduleRawCompactificationBaseChangeIso C b Λ) rfl
    (moduleCompactifiedBaseChangeMap_toDirectImage C.j C.p (C.baseChange b).j
      (pullback.fst b C.p) f (pullback.fst b f) C.fac (C.baseChange b).fac
      (pullback.snd b f) (pullback.snd b C.p) b
      (isPullback_rawCompactificationOpen C b) (IsPullback.of_hasPullback b C.p).flip
      pullback.condition Λ)
end AlgebraicGeometry.Scheme.EtaleCohomology
