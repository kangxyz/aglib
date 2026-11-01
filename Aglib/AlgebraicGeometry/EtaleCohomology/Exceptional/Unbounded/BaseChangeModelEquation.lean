/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.ModelTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ExceptionalBaseChange
public import Aglib.CategoryTheory.NatTrans.ExchangePastingTransport

/-! # Original normalized-model square for the chosen base-change map -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS wM wX' wT wN wR

variable {X S T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  [Nonempty (Hom.DenseCompactification f)] (b : T ⟶ S)

local instance unboundedNormalizedExchangeNonempty :
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

/-- At the actual normalized target, the original canonical self comparison
is the identity, so the chosen model square contains the original exchange itself. -/
theorem moduleExceptionalUnboundedBaseChange_normalized_model
    (C : Hom.DenseCompactification f) :
    ExchangeModelComparisonEquation
      (moduleExceptionalDirectImageUnboundedOfNonemptyIso f Λ N hN hΛ C)
      (moduleExceptionalDirectImageUnboundedOfNonemptyIso (pullback.fst b f) Λ N hN hΛ
        (Hom.DenseCompactification.baseChangeObj b C))
      (moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty f b Λ N hN hΛ).hom
      (moduleUnboundedNormalizedCompactificationBaseChangeIso C b Λ N hN hΛ).hom :=
  exchangeModelComparisonEquation_of_self (moduleUnboundedDerivedInverseImage Λ b)
    (moduleUnboundedDerivedInverseImage Λ (pullback.snd b f))
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso f Λ N hN hΛ C)
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso (pullback.fst b f) Λ N hN hΛ
      (Hom.DenseCompactification.baseChangeObj b C))
    (moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty f b Λ N hN hΛ)
    (moduleUnboundedNormalizedCompactificationBaseChangeIso C b Λ N hN hΛ)
    (moduleUnboundedCompactificationComparison (pullback.fst b f) Λ N hN hΛ
      (Hom.DenseCompactification.baseChangeObj b C) (Hom.DenseCompactification.baseChangeObj b C))
    (moduleUnboundedCompactificationComparison_self (pullback.fst b f) Λ N hN hΛ
      (Hom.DenseCompactification.baseChangeObj b C))
    (moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty_model f b Λ N hN hΛ C
      (Hom.DenseCompactification.baseChangeObj b C))

end AlgebraicGeometry.Scheme.EtaleCohomology
