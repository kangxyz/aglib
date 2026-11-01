/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.DirectImageCartesianFactor
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SourceIsoToDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ToDirectImageBaseChange

/-! # The same canonical comparison for a given Cartesian presentation -/
@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wL wT wX' wM wN wP wR
variable {X S X' T : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ T)
  (g : T ⟶ S) (g' : X' ⟶ X) (sq : IsPullback g' f' f g)
  [QuasiCompact f] [QuasiCompact f']
  [Nonempty (Hom.DenseCompactification f)]

local instance unboundedCartesianToTargetLiteralNonempty :
    Nonempty (Hom.DenseCompactification (pullback.fst g f)) :=
  ⟨Hom.DenseCompactification.baseChangeObj g (moduleExceptionalSuppliedCompactification f)⟩

variable [Nonempty (Hom.DenseCompactification f')]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wL} (ModuleSheaf (pullback g f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [sourceModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [literalModels : ∀ C : Hom.DenseCompactification (pullback.fst g f),
    HasDerivedCategory.{wN} (ModuleSheaf C.Xbar Λ)]
  [presentationModels : ∀ C : Hom.DenseCompactification f',
    HasDerivedCategory.{wP} (ModuleSheaf C.Xbar Λ)]
  [rawModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wR} (ModuleSheaf (pullback g C.p) Λ)]

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The original given-square !BC preserves the same canonical !→* map, independently
of all source, literal pullback, presentation and raw middle models. -/
theorem moduleExceptionalToDirectImageUnbounded_cartesianBaseChange :
    ExchangeToTargetEquation
      (moduleExceptionalToDirectImageUnboundedOfNonempty f Λ)
      (moduleExceptionalToDirectImageUnboundedOfNonempty f' Λ)
      (moduleExceptionalDirectImageUnboundedCartesianBaseChangeIsoOfNonempty
        f f' g g' sq Λ N hN hΛ).hom
      (moduleUnboundedDerivedBaseChangeMap Λ f f' g g' sq.w.symm) :=
  cartesianSource_toTarget
    (moduleExceptionalToDirectImageUnboundedOfNonempty f Λ)
    (moduleExceptionalToDirectImageUnboundedOfNonempty (pullback.fst g f) Λ)
    (moduleExceptionalToDirectImageUnboundedOfNonempty f' Λ)
    (moduleExceptionalDirectImageUnboundedBaseChangeIsoOfNonempty f g Λ N hN hΛ).hom
    (moduleUnboundedDerivedBaseChangeMap Λ f (pullback.fst g f) g (pullback.snd g f)
      pullback.condition)
    (moduleExceptionalDirectImageUnboundedSourceIsoOfNonempty (pullback.fst g f) f'
      sq.flip.isoPullback sq.flip.isoPullback_hom_fst Λ N hN hΛ).hom
    (moduleUnboundedDirectImageSourceTransport (pullback.fst g f) f'
      sq.flip.isoPullback sq.flip.isoPullback_hom_fst Λ)
    (moduleUnboundedCartesianBaseChangeSourceIso f f' g g' sq Λ)
    (moduleExceptionalDirectImageUnboundedCartesianBaseChangeIsoOfNonempty
      f f' g g' sq Λ N hN hΛ).hom
    (moduleUnboundedDerivedBaseChangeMap Λ f f' g g' sq.w.symm)
    (moduleExceptionalDirectImageUnboundedCartesianBaseChangeIsoOfNonempty_hom_app
      f f' g g' sq Λ N hN hΛ)
    (moduleExceptionalToDirectImageUnbounded_baseChange f g Λ N hN hΛ)
    (moduleExceptionalToDirectImageUnbounded_sourceIso (pullback.fst g f) f'
      sq.flip.isoPullback sq.flip.isoPullback_hom_fst Λ N hN hΛ)
    (moduleUnboundedDerivedBaseChangeMap_cartesian_factor f f' g g' sq Λ)
end AlgebraicGeometry.Scheme.EtaleCohomology
