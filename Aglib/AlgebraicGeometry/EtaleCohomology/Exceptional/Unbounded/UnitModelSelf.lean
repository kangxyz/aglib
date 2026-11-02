/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.UnitModelComparison

/-! # The explicitly same-model single-value comparison is the original chosen comparison -/

@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wX wS wM
variable {X S : Scheme.{u}} (f : X ⟶ S) [QuasiCompact f]
  (Λ : Type (u + 1)) [Ring Λ]
  [hX : HasDerivedCategory.{wX} (ModuleSheaf X Λ)]
  [hS : HasDerivedCategory.{wS} (ModuleSheaf S Λ)]
  [models : ∀ C : Hom.DenseCompactification f,
    HasDerivedCategory.{wM} (ModuleSheaf C.Xbar Λ)]
  (N : ℕ) (hN : 0 < N) (hΛ : N • (1 : Λ) = 0)

/-- The literal identity transition, with exactly the same model, is the identity. -/
theorem moduleUnboundedCompactificationSingleModelIso_self
    (C : Hom.DenseCompactification f) :
    moduleUnboundedCompactificationSingleModelIso f Λ N hN hΛ C (models C) = Iso.refl _ := by
  apply Iso.ext
  exact moduleUnboundedCompactificationTransition_id Λ C

variable [CompactSpace S] [QuasiSeparatedSpace S] [IsSeparated f] [LocallyOfFiniteType f]

/-- Specifying the original model introduces no new comparison map. -/
theorem moduleExceptionalUnboundedSingleValueIso_self
    (C : Hom.DenseCompactification f) :
    moduleExceptionalUnboundedSingleValueIso f Λ N hN hΛ C (models C) =
      moduleExceptionalDirectImageUnboundedIso f Λ N hN hΛ C := by
  rw [moduleExceptionalUnboundedSingleValueIso, moduleUnboundedCompactificationSingleModelIso_self]
  exact Iso.trans_refl _

end AlgebraicGeometry.Scheme.EtaleCohomology
