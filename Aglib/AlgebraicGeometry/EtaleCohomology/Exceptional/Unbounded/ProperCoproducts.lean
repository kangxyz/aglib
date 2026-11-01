/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ProperAmplitude
public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.ModuleCoefficientCoproducts
public import Aglib.Algebra.Homology.DerivedCategory.UnboundedRightDerived.Coproducts.Preservation

/-! # Actual proper unbounded direct image preserves arbitrary coproducts

The actual geometric relative bound and the original coefficient-continuity
comparisons discharge the hypotheses of the generic computation theorem.
The result concerns the original unbounded functor and its native coproduct
comparison on every family of native derived objects. The coefficient ring
is killed by a positive integer, without an invertibility assumption.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients

universe u wX wS

attribute [local instance] hasSheafifyLarge
  CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard

variable (Λ : Type (u + 1)) [Ring Λ] {X S : Scheme.{u}}
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [CompactSpace S] (f : X ⟶ S) [IsProper f]
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

include N hN hΛ

/-- The original unbounded direct image of a proper morphism with quasi-compact
target preserves arbitrary coproducts of the coefficient universe. -/
theorem moduleUnboundedDerivedDirectImage_preservesCoproducts_of_proper
    (κ : Type (u + 1)) :
    PreservesColimitsOfShape (Discrete κ) (moduleUnboundedDerivedDirectImage Λ f) := by
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} X)
  let := HasDerivedCategory.standard (AbelianSheaf.{u, u + 1} S)
  let : PreservesColimitsOfShape (Discrete κ) (moduleDirectImage f Λ) :=
    moduleDirectImage_preservesCoproducts Λ f κ
  let (n : ℕ) : PreservesColimitsOfShape (Discrete κ)
      ((moduleDirectImage f Λ).rightDerived (n + 1)) :=
    moduleRightDerived_preservesCoproducts Λ f (n + 1) κ
  obtain ⟨d, hd⟩ := exists_moduleRightDerived_bound_of_proper Λ f N hN hΛ
  exact (moduleDirectImage f Λ).unboundedRightDerived_preservesCoproducts_of_bound d hd

/-- Invertibility concerns the native universal coproduct comparison, whose
components are the images of the original summand inclusions. -/
theorem isIso_moduleUnboundedDerivedDirectImage_sigmaComparison
    {κ : Type (u + 1)} (K : κ → DerivedCategory (ModuleSheaf X Λ)) :
    IsIso (sigmaComparison (moduleUnboundedDerivedDirectImage Λ f) K) := by
  let := moduleUnboundedDerivedDirectImage_preservesCoproducts_of_proper Λ f N hN hΛ κ
  infer_instance

end AlgebraicGeometry.Scheme.EtaleCohomology.Coefficients
