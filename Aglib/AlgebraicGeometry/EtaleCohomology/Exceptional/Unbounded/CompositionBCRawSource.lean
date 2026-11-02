/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.CategoryTheory.NatTrans.CartesianExchangePasting
public import Aglib.AlgebraicGeometry.Compactification.Refinements.CompositionBaseChangeGeometry
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawSourceIsoPasting
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawSquareCongruence
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.CartesianBaseChange

/-! # The original raw exchange in a given Cartesian presentation -/

@[expose] public noncomputable section
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wL wT wX' wM wR

variable {X S X' T : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ T)
  (b : T ⟶ S) (a : X' ⟶ X) (sq : IsPullback a f' f b)
  (C : Hom.Compactification f) (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wL} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wX'} (ModuleSheaf X' Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ)]

/-- The local derived-category model on `ModuleSheaf (C.baseChange b).Xbar Λ`. -/
local instance unboundedCompositionRawSourceLiteralModel :
    HasDerivedCategory.{wR} (ModuleSheaf (C.baseChange b).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ))
/-- The local derived-category model on `ModuleSheaf (C.cartesianBaseChange f' a b sq).Xbar Λ`. -/
local instance unboundedCompositionRawSourceTransportModel :
    HasDerivedCategory.{wR}
      (ModuleSheaf (C.cartesianBaseChange f' a b sq).Xbar Λ) :=
  inferInstanceAs (HasDerivedCategory.{wR} (ModuleSheaf (pullback b C.p) Λ))

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- Actual universal source transport computes the given raw Cartesian exchange. -/
theorem moduleUnboundedRawCartesianPresentation :
    (cartesianSourceExchange (moduleUnboundedRawCompactificationBaseChangeIso C b Λ N hN hΛ)
      (moduleUnboundedRawCompactificationSourceIso sq.flip.isoPullback Λ f'
        sq.flip.isoPullback_hom_fst (C.baseChange b))
      (moduleUnboundedCartesianBaseChangeSourceIso f f' b a sq Λ)).hom =
    moduleUnboundedRawSquareMap C (C.cartesianBaseChange f' a b sq) a (pullback.snd b C.p) b
      (Hom.Compactification.isPullback_cartesianBaseChange_open C f' a b sq)
      (IsPullback.of_hasPullback b C.p).flip Λ := by
  let e := sq.flip.isoPullback
  let hj := isPullback_rawCompactificationOpen C b
  have ht : IsPullback (e.hom ≫ pullback.snd b f) (e.hom ≫ (C.baseChange b).j)
      C.j (pullback.snd b C.p) := by
    have h := (isPullback_sourceIsoOpen e (C.baseChange b).j).paste_horiz hj
    have hid : 𝟙 (C.baseChange b).Xbar ≫ pullback.snd b C.p = pullback.snd b C.p :=
      Category.id_comp _
    exact hid ▸ h
  exact cartesianExchangePasting (moduleUnboundedRawCompactificationBaseChangeIso C b Λ N hN hΛ)
    (moduleUnboundedRawCompactificationSourceIso e Λ f' sq.flip.isoPullback_hom_fst
      (C.baseChange b))
    (moduleUnboundedDerivedInverseImageCompIso Λ (pullback.snd b f) e.hom)
    (eqToIso (congrArg (fun z => moduleUnboundedDerivedInverseImage Λ z)
      sq.flip.isoPullback_hom_snd.symm))
    (moduleUnboundedRawSquareMap C (C.cartesianBaseChange f' a b sq)
      (e.hom ≫ pullback.snd b f) (pullback.snd b C.p) b ht
      (IsPullback.of_hasPullback b C.p).flip Λ)
    (moduleUnboundedRawSquareMap C (C.cartesianBaseChange f' a b sq) a (pullback.snd b C.p) b
      (Hom.Compactification.isPullback_cartesianBaseChange_open C f' a b sq)
      (IsPullback.of_hasPullback b C.p).flip Λ)
    (moduleUnboundedRawSquareMap_sourceIso_pasting C (C.baseChange b) (pullback.snd b f)
      (pullback.snd b C.p) b e f' sq.flip.isoPullback_hom_fst hj
      (IsPullback.of_hasPullback b C.p).flip ht Λ)
    (moduleUnboundedRawSquareMap_congr_source C (C.cartesianBaseChange f' a b sq) a
      (e.hom ≫ pullback.snd b f) sq.flip.isoPullback_hom_snd.symm
      (pullback.snd b C.p) b
      (Hom.Compactification.isPullback_cartesianBaseChange_open C f' a b sq) ht
      (IsPullback.of_hasPullback b C.p).flip Λ)

end AlgebraicGeometry.Scheme.EtaleCohomology
