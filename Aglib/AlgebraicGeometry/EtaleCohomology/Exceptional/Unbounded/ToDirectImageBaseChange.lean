/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ExceptionalBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SuppliedToDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.NormalizedToDirectImageBaseChange

/-! # The same original canonical exceptional comparison commutes with arbitrary base change -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM wX' wT wN wR

variable {X S T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  [Nonempty (Hom.DenseCompactification f)] (b : T ⟶ S)

local instance unboundedToDirectImageBaseChangeNonempty :
    Nonempty (Hom.DenseCompactification (pullback.fst b f)) :=
  ⟨Hom.DenseCompactification.baseChangeObj b (moduleExceptionalSuppliedCompactification f)⟩

variable (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [sourceModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [targetModels : ∀ C : Hom.DenseCompactification (pullback.fst b f),
    HasDerivedCategory.{wN} (ModuleSheaf C.Xbar Λ)]
  [rawModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ)]

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)


omit [Nonempty (Hom.DenseCompactification f)] in
/-- Canonical target-model transport retains the original structural base-change square. -/
theorem moduleUnboundedCompactificationBaseChangeIsoTo_toDirectImage
    (C : Hom.DenseCompactification f) (D : Hom.DenseCompactification (pullback.fst b f)) :
    ExchangeToTargetEquation (moduleUnboundedCompactificationToDirectImage f Λ C)
      (moduleUnboundedCompactificationToDirectImage (pullback.fst b f) Λ D)
      (moduleUnboundedCompactificationBaseChangeIsoTo f b Λ N hN hΛ C D).hom
      (moduleUnboundedDerivedBaseChangeMap Λ f (pullback.fst b f) b (pullback.snd b f)
        pullback.condition) :=
  exchangeToTarget_postcompose
    (moduleUnboundedCompactificationToDirectImage f Λ C)
    (moduleUnboundedCompactificationToDirectImage (pullback.fst b f) Λ
      (Hom.DenseCompactification.baseChangeObj b C))
    (moduleUnboundedCompactificationToDirectImage (pullback.fst b f) Λ D)
    (moduleUnboundedCompactificationComparison (pullback.fst b f) Λ N hN hΛ
      (Hom.DenseCompactification.baseChangeObj b C) D).hom
    (moduleUnboundedNormalizedCompactificationBaseChangeIso C b Λ N hN hΛ).hom
    (moduleUnboundedDerivedBaseChangeMap Λ f (pullback.fst b f) b (pullback.snd b f)
      pullback.condition)
    (moduleUnboundedCompactificationToDirectImage_comparison (pullback.fst b f) Λ N hN hΛ
      (Hom.DenseCompactification.baseChangeObj b C) D)
    (moduleUnboundedNormalizedCompactificationBaseChangeIso_toDirectImage C b Λ N hN hΛ)

/-- The accepted chosen exceptional exchange preserves the same original canonical map.
The new base is arbitrary; compactifiability is supplied by actual normalized pullback. -/
theorem moduleExceptionalToDirectImageUnbounded_baseChange :
    ExchangeToTargetEquation (moduleExceptionalToDirectImageUnboundedOfNonempty f Λ)
      (moduleExceptionalToDirectImageUnboundedOfNonempty (pullback.fst b f) Λ)
      (moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty f b Λ N hN hΛ).hom
      (moduleUnboundedDerivedBaseChangeMap Λ f (pullback.fst b f) b (pullback.snd b f)
        pullback.condition) :=
  moduleUnboundedCompactificationBaseChangeIsoTo_toDirectImage f b Λ N hN hΛ
    (moduleExceptionalSuppliedCompactification f)
    (moduleExceptionalSuppliedCompactification (pullback.fst b f))
end AlgebraicGeometry.Scheme.EtaleCohomology
