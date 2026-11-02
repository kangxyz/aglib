/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.SourceExchange.ModelTransport
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.BoundedBelow.BaseChange
public import Aglib.CategoryTheory.NatTrans.ExchangePastingTransport

/-! # Original normalized-model square for the chosen base-change map -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS wM wX' wT wN wR

variable {X S T : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  [Nonempty (Hom.DenseCompactification f)] (b : T ⟶ S)

local instance : Nonempty (Hom.DenseCompactification (pullback.fst b f)) :=
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

/-- At the actual normalized target, the original canonical self comparison
is the identity, so the chosen model square contains the original exchange itself. -/
theorem moduleExceptionalBaseChange_normalized_model
    (C : Hom.DenseCompactification f) :
    ExchangeModelComparisonEquation
      (moduleExceptionalDirectImagePlusOfNonemptyIso f Λ C)
      (moduleExceptionalDirectImagePlusOfNonemptyIso (pullback.fst b f) Λ
        (Hom.DenseCompactification.baseChangeObj b C))
      (moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty f b Λ).hom
      (moduleNormalizedCompactificationBaseChangeIso C b Λ).hom :=
  exchangeModelComparisonEquation_of_self (moduleDerivedInverseImage Λ b)
    (moduleDerivedInverseImageTorsion (pullback.snd b f) Λ)
    (moduleExceptionalDirectImagePlusOfNonemptyIso f Λ C)
    (moduleExceptionalDirectImagePlusOfNonemptyIso (pullback.fst b f) Λ
      (Hom.DenseCompactification.baseChangeObj b C))
    (moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty f b Λ)
    (moduleNormalizedCompactificationBaseChangeIso C b Λ)
    (moduleCompactificationComparison (pullback.fst b f) Λ
      (Hom.DenseCompactification.baseChangeObj b C) (Hom.DenseCompactification.baseChangeObj b C))
    (moduleCompactificationComparison_self (pullback.fst b f) Λ
      (Hom.DenseCompactification.baseChangeObj b C))
    (moduleExceptionalDirectImagePlusBaseChangeIsoOfNonempty_model f b Λ C
      (Hom.DenseCompactification.baseChangeObj b C))

end AlgebraicGeometry.Scheme.EtaleCohomology
