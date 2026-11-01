/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ExceptionalBaseChange
public import Aglib.CategoryTheory.NatTrans.IdentityFunctorNormalizer
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.IdentitySourceModel

/-!
# Chosen identity base change in a common base model

The identity-specific source transport is defined from the original source
isomorphism, original mixed-model refinement unit, and canonical target
comparison, never from base change. Its model independence follows from the
proved original identity normalization and original base-change model equation.
Source and target compactification-model families remain independent. Only the
base derived model is common; independently chosen copies of that same base
require the separate canonical native-model transport.
-/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS wX' wM wN wR
variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  [Nonempty (Hom.DenseCompactification f)]
local instance unboundedIdentityPullbackNonempty :
    Nonempty (Hom.DenseCompactification (pullback.fst (𝟙 S) f)) :=
  ⟨Hom.DenseCompactification.baseChangeObj (𝟙 S) (moduleExceptionalSuppliedCompactification f)⟩

variable (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf (pullback (𝟙 S) f) Λ)]
  [sourceModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [targetModels : ∀ C : Hom.DenseCompactification (pullback.fst (𝟙 S) f),
    HasDerivedCategory.{wN} (ModuleSheaf C.Xbar Λ)]

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- Identity-specific source transport to a specified target model, defined
from original geometry and original unit comparisons rather than base change. -/
def moduleUnboundedIdentitySourceModelIsoTo
    (C : Hom.DenseCompactification f)
    (D : Hom.DenseCompactification (pullback.fst (𝟙 S) f)) :
    moduleUnboundedCompactificationFunctor f Λ C ≅
      moduleUnboundedDerivedInverseImage Λ (pullback.snd (𝟙 S) f) ⋙
        moduleUnboundedCompactificationFunctor (pullback.fst (𝟙 S) f) Λ D :=
  moduleUnboundedIdentitySourceModelIso C Λ N hN hΛ ≪≫
    Functor.isoWhiskerLeft (moduleUnboundedDerivedInverseImage Λ (pullback.snd (𝟙 S) f))
      (moduleUnboundedCompactificationComparison (pullback.fst (𝟙 S) f) Λ N hN hΛ
        (Hom.DenseCompactification.baseChangeObj (𝟙 S) C) D)

/-- Identity-specific chosen source transport, with no base-change map in its definition. -/
def moduleExceptionalUnboundedIdentitySourceIsoOfNonempty :
    moduleExceptionalDirectImageUnboundedOfNonempty f Λ ≅
      moduleUnboundedDerivedInverseImage Λ (pullback.snd (𝟙 S) f) ⋙
        moduleExceptionalDirectImageUnboundedOfNonempty (pullback.fst (𝟙 S) f) Λ :=
  moduleUnboundedIdentitySourceModelIsoTo f Λ N hN hΛ (moduleExceptionalSuppliedCompactification f)
    (moduleExceptionalSuppliedCompactification (pullback.fst (𝟙 S) f))

variable [rawModels : ∀ C : Hom.DenseCompactification f,
  HasDerivedCategory.{wR} (ModuleSheaf (pullback (𝟙 S) C.p) Λ)]

omit [Nonempty (Hom.DenseCompactification f)] in
/-- The actual original identity normalization at any two supplied models. -/
theorem moduleUnboundedCompactificationBaseChangeIsoTo_identity
    (C : Hom.DenseCompactification f)
    (D : Hom.DenseCompactification (pullback.fst (𝟙 S) f)) :
    moduleUnboundedCompactificationBaseChangeIsoTo f (𝟙 S) Λ N hN hΛ C D =
      identityFunctorNormalizer (moduleUnboundedCompactificationFunctor f Λ C)
        (moduleUnboundedDerivedInverseImageIdIso Λ S) ≪≫
        moduleUnboundedIdentitySourceModelIsoTo f Λ N hN hΛ C D :=
  identityBaseChange_postcomp
    (moduleUnboundedNormalizedCompactificationBaseChangeIso C (𝟙 S) Λ N hN hΛ)
    (moduleUnboundedDerivedInverseImageIdIso Λ S)
        (moduleUnboundedIdentitySourceModelIso C Λ N hN hΛ)
    (moduleUnboundedCompactificationComparison (pullback.fst (𝟙 S) f) Λ N hN hΛ
      (Hom.DenseCompactification.baseChangeObj (𝟙 S) C) D)
    (moduleUnboundedNormalizedBaseChange_identity_sourceModel C Λ N hN hΛ)

/-- Chosen identity base change has the original identity normalization. -/
theorem moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty_identity :
    moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty f (𝟙 S) Λ N hN hΛ =
      identityFunctorNormalizer (moduleExceptionalDirectImageUnboundedOfNonempty f Λ)
        (moduleUnboundedDerivedInverseImageIdIso Λ S) ≪≫
      moduleExceptionalUnboundedIdentitySourceIsoOfNonempty f Λ N hN hΛ :=
  moduleUnboundedCompactificationBaseChangeIsoTo_identity f Λ N hN hΛ
    (moduleExceptionalSuppliedCompactification f)
    (moduleExceptionalSuppliedCompactification (pullback.fst (𝟙 S) f))

/-- The separately defined identity-specific source transport is independent
of the supplied source and target compactifications through original comparisons. -/
theorem moduleExceptionalUnboundedIdentitySourceIsoOfNonempty_model
    (C : Hom.DenseCompactification f)
    (D : Hom.DenseCompactification (pullback.fst (𝟙 S) f)) :
    moduleExceptionalDirectImageUnboundedOfNonemptyIso f Λ N hN hΛ C ≪≫
        moduleUnboundedIdentitySourceModelIsoTo f Λ N hN hΛ C D =
      moduleExceptionalUnboundedIdentitySourceIsoOfNonempty f Λ N hN hΛ ≪≫
        Functor.isoWhiskerLeft (moduleUnboundedDerivedInverseImage Λ (pullback.snd (𝟙 S) f))
          (moduleExceptionalDirectImageUnboundedOfNonemptyIso (pullback.fst (𝟙 S) f) Λ N hN hΛ D) :=
  identitySourceTransport_model
    (moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty f (𝟙 S) Λ N hN hΛ)
    (moduleUnboundedCompactificationBaseChangeIsoTo f (𝟙 S) Λ N hN hΛ C D)
    (moduleExceptionalUnboundedIdentitySourceIsoOfNonempty f Λ N hN hΛ)
    (moduleUnboundedIdentitySourceModelIsoTo f Λ N hN hΛ C D)
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso f Λ N hN hΛ C)
    (moduleExceptionalDirectImageUnboundedOfNonemptyIso (pullback.fst (𝟙 S) f) Λ N hN hΛ D)
    (moduleUnboundedDerivedInverseImageIdIso Λ S)
    (moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty_model f (𝟙 S) Λ N hN hΛ C D)
    (moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty_identity f Λ N hN hΛ)
    (moduleUnboundedCompactificationBaseChangeIsoTo_identity f Λ N hN hΛ C D)

end AlgebraicGeometry.Scheme.EtaleCohomology
