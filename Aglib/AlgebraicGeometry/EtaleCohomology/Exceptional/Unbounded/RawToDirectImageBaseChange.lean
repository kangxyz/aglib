/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompactifiedToDirectImageBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawToDirectImage
public import Aglib.CategoryTheory.NatTrans.ExchangeToTarget

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
local instance unboundedRawToDirectImageBaseChangeModel :
    HasDerivedCategory.{wR} (ModuleSheaf (C.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ))

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- Literal raw pullback exchange preserves the same canonical map on all objects. -/
theorem moduleUnboundedRawCompactificationBaseChangeIso_toDirectImage :
    ExchangeToTargetEquation (moduleUnboundedRawCompactificationToDirectImage C Λ)
      (moduleUnboundedRawCompactificationToDirectImage (C.baseChange b) Λ)
      (moduleUnboundedRawCompactificationBaseChangeIso C b Λ N hN hΛ).hom
      (moduleUnboundedDerivedBaseChangeMap Λ f (pullback.fst b f) b (pullback.snd b f)
        pullback.condition) :=
  moduleUnboundedCompactifiedBaseChangeMap_toDirectImage C.j C.p (C.baseChange b).j
    (pullback.fst b C.p) f (pullback.fst b f) C.fac (C.baseChange b).fac
    (pullback.snd b f) (pullback.snd b C.p) b
    (isPullback_rawCompactificationOpen C b) (IsPullback.of_hasPullback b C.p).flip
    pullback.condition Λ
end AlgebraicGeometry.Scheme.EtaleCohomology
