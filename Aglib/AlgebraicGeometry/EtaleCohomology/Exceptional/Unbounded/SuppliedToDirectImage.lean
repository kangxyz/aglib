/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.SuppliedDirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ToDirectImageNaturality

/-! # The same canonical comparison for a supplied compactifiable morphism -/
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
  [middleModels : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- The original model map, selected by the same supplied compactification as the functor. -/
def moduleExceptionalToDirectImageUnboundedOfNonempty :
    moduleExceptionalDirectImageUnboundedOfNonempty f Λ ⟶
      moduleUnboundedDerivedDirectImage Λ f :=
  moduleUnboundedCompactificationToDirectImage f Λ (moduleExceptionalSuppliedCompactification f)

variable (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The same map is computed through every original compactification, with no qcqs base premise. -/
theorem moduleExceptionalToDirectImageUnboundedOfNonempty_model
    (C : Hom.DenseCompactification f) :
    TargetComparisonEquation (moduleExceptionalDirectImageUnboundedOfNonemptyIso f Λ N hN hΛ C).hom
      (moduleUnboundedCompactificationToDirectImage f Λ C)
      (moduleExceptionalToDirectImageUnboundedOfNonempty f Λ) :=
  moduleUnboundedCompactificationToDirectImage_comparison f Λ N hN hΛ
    (moduleExceptionalSuppliedCompactification f) C
end AlgebraicGeometry.Scheme.EtaleCohomology
