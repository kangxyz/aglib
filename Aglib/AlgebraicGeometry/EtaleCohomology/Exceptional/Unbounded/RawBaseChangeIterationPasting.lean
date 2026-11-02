/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.BaseChangeIterationCompatibility
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.RawBaseChange
public import Aglib.AlgebraicGeometry.Compactification.Refinements.RawCartesianIteration

/-!
# Original consecutive full-unbounded raw base change

The composite map lands on the literal iterated raw compactification. The
original native exchange pasting proves the equation without a boundedness
test or restriction transport. Normalized and chosen comparisons are separate.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wM wX₁ wT wM₁ wX₂ wU wM₂

variable {X S T U : Scheme.{u}} {f : X ⟶ S}
  (C : Hom.Compactification f) (b : T ⟶ S) (c : U ⟶ T)

variable (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  [HasDerivedCategory.{wX₁} (ModuleSheaf (pullback b f) Λ)]
  [HasDerivedCategory.{wT} (ModuleSheaf T Λ)]
  [HasDerivedCategory.{wM₁} (ModuleSheaf ((C.baseChange b)).Xbar Λ)]
  [HasDerivedCategory.{wX₂} (ModuleSheaf (pullback c (pullback.fst b f)) Λ)]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wM₂} (ModuleSheaf (((C.baseChange b).baseChange c)).Xbar Λ)]

/-- The derived-category instance in universe `wM₁` for `Λ`-module sheaves on `(pullback b C.p)`.
-/
local instance unboundedRawIterationFirstNativeModel :
    HasDerivedCategory.{wM₁} (ModuleSheaf (pullback b C.p) Λ) :=
  inferInstanceAs (HasDerivedCategory.{wM₁} (ModuleSheaf ((C.baseChange b)).Xbar Λ))
/-- The derived-category instance in universe `wM₂` for `Λ`-module sheaves on `(pullback c
    ((C.baseChange b)).p)`.
-/
local instance unboundedRawIterationSecondNativeModel :
    HasDerivedCategory.{wM₂} (ModuleSheaf (pullback c ((C.baseChange b)).p) Λ) :=
  inferInstanceAs (HasDerivedCategory.{wM₂} (ModuleSheaf (((C.baseChange b).baseChange c)).Xbar Λ))

/-- The original native unbounded composite exchange on the literal iterated raw model. -/
def moduleUnboundedRawIterationCompositeMap :=
  moduleUnboundedCompactifiedBaseChangeMap C.j C.p (((C.baseChange b).baseChange c)).j
    (((C.baseChange b).baseChange c)).p
    ((pullback.snd c (pullback.fst b f)) ≫ (pullback.snd b f))
    ((pullback.snd c (C.baseChange b).p) ≫ (pullback.snd b C.p)) (c ≫ b)
    (isPullback_rawIterationOpen C b c) (isPullback_rawIterationProper C b c) Λ

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- Consecutive original full-unbounded raw exchanges satisfy actual compositor pasting. -/
theorem moduleUnboundedRawBaseChangeIteration_pasting :
    ∀ K, ActualHorizontalMateEquation
      (moduleUnboundedRawCompactificationBaseChangeIso C b Λ N hN hΛ).hom
      (moduleUnboundedRawCompactificationBaseChangeIso (C.baseChange b) c Λ N hN hΛ).hom
      (moduleUnboundedRawIterationCompositeMap C b c Λ)
      (moduleUnboundedDerivedInverseImageCompIso Λ b c).hom
      (moduleUnboundedDerivedInverseImageCompIso Λ (pullback.snd b f)
        (pullback.snd c (pullback.fst b f))).hom K :=
  moduleUnboundedCompactifiedBaseChangeMap_pasting C.j C.p ((C.baseChange b)).j ((C.baseChange b)).p
      (((C.baseChange b).baseChange c)).j (((C.baseChange b).baseChange c)).p
      (pullback.snd b f) (pullback.snd b C.p) b (pullback.snd c (pullback.fst b f)) (pullback.snd
        c (C.baseChange b).p) c (isPullback_rawCompactificationOpen C b)
      (IsPullback.of_hasPullback b C.p).flip (isPullback_rawCompactificationOpen (C.baseChange b) c)
      (IsPullback.of_hasPullback c ((C.baseChange b)).p).flip (isPullback_rawIterationOpen C b c)
      (isPullback_rawIterationProper C b c) Λ

end AlgebraicGeometry.Scheme.EtaleCohomology
