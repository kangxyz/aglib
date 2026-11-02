/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.DirectImage
public import Aglib.AlgebraicGeometry.Compactification.Refinements.Supplied

/-! # Actual unbounded exceptional image on a supplied compactifiable morphism

Only the existing geometric choice from a nonempty dense-compactification
category is reused. The value and canonical comparisons are the genuine
unbounded construction. In particular no qcqs hypothesis on a new base is needed.
-/

@[expose] public noncomputable section

open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients

universe u wX wS wM
variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  [Nonempty (Hom.DenseCompactification f)]
  (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]

section Value
variable [chosenMiddleModel : HasDerivedCategory.{wM}
  (ModuleSheaf (moduleExceptionalSuppliedCompactification f).Xbar Λ)]

/-- The original unbounded model at the existing supplied geometric compactification. -/
def moduleExceptionalDirectImageUnboundedOfNonempty :
    DerivedCategory (ModuleSheaf X Λ) ⥤ DerivedCategory (ModuleSheaf S Λ) :=
  moduleUnboundedCompactificationFunctor f Λ (moduleExceptionalSuppliedCompactification f)

variable [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]

/-- On the Nagata range this is literally the existing unbounded exceptional functor. -/
theorem moduleExceptionalDirectImageUnboundedOfNonempty_eq :
    moduleExceptionalDirectImageUnboundedOfNonempty f Λ =
      (letI : HasDerivedCategory.{wM}
          (ModuleSheaf (moduleExceptionalCompactification f).Xbar Λ) := chosenMiddleModel
       moduleExceptionalDirectImageUnbounded f Λ) := rfl

end Value

variable
  [middleModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- Canonical comparison with any supplied model through the original refinement diagram. -/
def moduleExceptionalDirectImageUnboundedOfNonemptyIso (C : Hom.DenseCompactification f) :
    moduleExceptionalDirectImageUnboundedOfNonempty f Λ ≅
      moduleUnboundedCompactificationFunctor f Λ C :=
  moduleUnboundedCompactificationComparison f Λ N hN hΛ
    (moduleExceptionalSuppliedCompactification f) C

/-- The comparisons retain the actual original cocycle. -/
theorem moduleExceptionalDirectImageUnboundedOfNonemptyIso_trans
    (C D : Hom.DenseCompactification f) :
    moduleExceptionalDirectImageUnboundedOfNonemptyIso f Λ N hN hΛ C ≪≫
      moduleUnboundedCompactificationComparison f Λ N hN hΛ C D =
    moduleExceptionalDirectImageUnboundedOfNonemptyIso f Λ N hN hΛ D :=
  moduleUnboundedCompactificationComparison_trans f Λ N hN hΛ
    (moduleExceptionalSuppliedCompactification f) C D


end AlgebraicGeometry.Scheme.EtaleCohomology
