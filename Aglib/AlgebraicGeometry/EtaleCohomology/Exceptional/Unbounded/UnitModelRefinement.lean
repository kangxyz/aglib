/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.UnitModelComparison

/-! # Original invertible mixed transitions between single unbounded values -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM wC wD
variable {X S : Scheme.{u}} {f : X ⟶ S} [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  {C D : Hom.DenseCompactification f} (a : C ⟶ D)
  (hC : HasDerivedCategory.{wC} (ModuleSheaf C.Xbar Λ))
  (hD : HasDerivedCategory.{wD} (ModuleSheaf D.Xbar Λ))
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The actual mixed refinement, with its already proved invertibility recorded. -/
def moduleUnboundedCompactificationSingleTransitionIso :
    @moduleUnboundedCompactificationFunctor X S f Λ _ hX hS D hD ≅
      @moduleUnboundedCompactificationFunctor X S f Λ _ hX hS C hC :=
  @asIso _ _ _ _
    (@moduleUnboundedCompactificationMixedTransition X S f _ Λ _ hX hS C D a hC hD)
    (@moduleUnboundedCompactificationMixedTransition_isIso X S f _ Λ _ hX hS
      C D a hC hD N hN hΛ)

variable (f) [models : ∀ E : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf E.Xbar Λ)]
  [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]

/-- The isomorphism square retains the same original refinement homomorphism. -/
theorem moduleExceptionalUnboundedSingleValueIso_refinementIso :
    moduleExceptionalUnboundedSingleValueIso f Λ N hN hΛ D hD ≪≫
      moduleUnboundedCompactificationSingleTransitionIso Λ a hC hD N hN hΛ =
    moduleExceptionalUnboundedSingleValueIso f Λ N hN hΛ C hC := by
  apply Iso.ext
  exact moduleExceptionalUnboundedSingleValueIso_refinement f Λ N hN hΛ a hC hD

end AlgebraicGeometry.Scheme.EtaleCohomology
