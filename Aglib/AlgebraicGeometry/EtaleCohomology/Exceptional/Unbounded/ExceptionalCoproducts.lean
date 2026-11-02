/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.DirectImage
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperCoproducts
public import Mathlib.CategoryTheory.Adjunction.Limits

/-! # Arbitrary coproducts for the original chosen unbounded exceptional image

Actual open extension is a left adjoint and actual proper R* preserves arbitrary
coefficient-universe coproducts over a torsion ring. Canonical compactification
comparisons transport this property without changing the original functor.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.EtaleCohomology

open Coefficients

universe u wX wS wM

variable {X S : Scheme.{u}} [CompactSpace S]
  (f : X ⟶ S) [QuasiCompact f] (Λ : Type (u + 1)) [Ring Λ]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

include N hN hΛ

omit [QuasiCompact f] in
/-- Every actual compactification value preserves arbitrary coefficient-universe coproducts. -/
theorem moduleUnboundedCompactificationFunctor_preservesCoproducts
    (C : Hom.DenseCompactification f)
    [HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)] (κ : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete κ) (moduleUnboundedCompactificationFunctor f Λ C) := by
  let := (moduleUnboundedDerivedLowerShriekAdjunction C.j Λ).isLeftAdjoint
  let := moduleUnboundedDerivedDirectImage_preservesCoproducts_of_proper Λ C.p N hN hΛ κ
  change PreservesColimitsOfShape (Discrete κ)
    (moduleUnboundedDerivedLowerShriek C.j Λ ⋙ moduleUnboundedDerivedDirectImage Λ C.p)
  infer_instance

variable [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]

section Value

variable [HasDerivedCategory.{wM}
  (ModuleSheaf (moduleExceptionalCompactification f).Xbar Λ)]

/-- The original chosen unbounded exceptional image preserves arbitrary coproducts. -/
theorem moduleExceptionalDirectImageUnbounded_preservesCoproducts (κ : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete κ) (moduleExceptionalDirectImageUnbounded f Λ) :=
  moduleUnboundedCompactificationFunctor_preservesCoproducts f Λ N hN hΛ
    (moduleExceptionalCompactification f) κ

/-- The canonical sigma comparison, with the original summand inclusions, is invertible. -/
theorem isIso_moduleExceptionalDirectImageUnbounded_sigmaComparison
    {κ : Type (u + 1)} (K : κ → DerivedCategory (ModuleSheaf X Λ)) :
    IsIso (sigmaComparison (moduleExceptionalDirectImageUnbounded f Λ) K) := by
  let := moduleExceptionalDirectImageUnbounded_preservesCoproducts f Λ N hN hΛ κ
  infer_instance

end Value

variable [middleModels : ∀ C : Hom.DenseCompactification f,
  HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]

/-- The same property can be computed using any supplied compactification. -/
theorem moduleExceptionalDirectImageUnbounded_preservesCoproducts_of_model
    (C : Hom.DenseCompactification f) (κ : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete κ) (moduleExceptionalDirectImageUnbounded f Λ) := by
  let := moduleUnboundedCompactificationFunctor_preservesCoproducts f Λ N hN hΛ C κ
  exact preservesColimitsOfShape_of_natIso
    (moduleExceptionalDirectImageUnboundedIso f Λ N hN hΛ C).symm

end AlgebraicGeometry.Scheme.EtaleCohomology
