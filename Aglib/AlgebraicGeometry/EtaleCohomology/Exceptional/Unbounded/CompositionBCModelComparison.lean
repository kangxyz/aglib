/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import
  Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CompositionBaseChangeChosenModel
public import Aglib.CategoryTheory.NatTrans.ExchangePastingTransport

/-! # Original chosen full-unbounded exchange on actual independent dense models -/
@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wL wT wX' wM wN wP wR

variable {X S X' T : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ T)
  (b : T ⟶ S) (a : X' ⟶ X) (sq : IsPullback a f' f b)
  [QuasiCompact f] [QuasiCompact f']
  [Nonempty (Hom.DenseCompactification f)]
  [Nonempty (Hom.DenseCompactification f')]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [hL : HasDerivedCategory.{wL} (ModuleSheaf (pullback b f) Λ)]
  [hT : HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [hX' : HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [sourceModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [literalModels : ∀ D : Hom.DenseCompactification (pullback.fst b f),
    HasDerivedCategory.{wN} (ModuleSheaf D.Xbar Λ)]
  [presentationModels : ∀ E : Hom.DenseCompactification f',
    HasDerivedCategory.{wP} (ModuleSheaf E.Xbar Λ)]
  [rawModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ)]
  (C : Hom.DenseCompactification f) (E : Hom.DenseCompactification f')
  (q : E.Xbar ⟶ C.Xbar) (hj : IsPullback a E.j C.j q) (hp : q ≫ C.p = E.p ≫ b)


/-- The local derived-category model on `ModuleSheaf C.Xbar Λ`. -/
local instance unboundedCompositionComparisonOldModel : HasDerivedCategory.{wM} (ModuleSheaf
  C.Xbar Λ) :=
  sourceModels C
/-- The local derived-category model on `ModuleSheaf E.Xbar Λ`. -/
local instance unboundedCompositionComparisonNewModel : HasDerivedCategory.{wP} (ModuleSheaf
  E.Xbar Λ) :=
  presentationModels E


variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The existing chosen comparison retains its original actual dense-model equation. -/
theorem moduleExceptionalUnboundedCartesianBaseChange_commuting_model :
    ExchangeModelComparisonEquation
      (moduleExceptionalDirectImageUnboundedOfNonemptyIso f Λ N hN hΛ C)
      (moduleExceptionalDirectImageUnboundedOfNonemptyIso f' Λ N hN hΛ E)
      (moduleExceptionalDirectImageUnboundedCartesianBaseChangeIsoOfNonempty
        f f' b a sq Λ N hN hΛ).hom
      (moduleUnboundedRawCommutingSquareMap C.toCompactification E.toCompactification
        a q b hj hp.symm Λ) := by
  have he := congrArg Iso.hom
    (moduleExceptionalDirectImageUnboundedCartesianBaseChangeIsoOfNonempty_model
      f f' b a sq Λ N hN hΛ C (Hom.DenseCompactification.baseChangeObj b C) E)
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom] at he
  rw [moduleUnboundedCompactificationCartesianBaseChangeIsoTo_commuting
    f f' b a sq Λ C E q hj hp N hN hΛ] at he
  exact he

end AlgebraicGeometry.Scheme.EtaleCohomology
