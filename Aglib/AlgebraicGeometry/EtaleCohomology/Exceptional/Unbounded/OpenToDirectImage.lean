/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Exceptional.Unbounded.OpenFullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Triple

/-! # The original canonical comparison for unbounded open extension -/
@[expose] public noncomputable section
open CategoryTheory
namespace AlgebraicGeometry.Scheme.EtaleCohomology
open Coefficients
universe u wU wX
variable (Λ : Type (u + 1)) [Ring Λ] {U X : Scheme.{u}}
  (j : U ⟶ X) [IsOpenImmersion j]
  [HasDerivedCategory.{wU} (ModuleSheaf U Λ)]
  [HasDerivedCategory.{wX} (ModuleSheaf X Λ)]

/-- The actual native unbounded adjoint triple, with both installed adjunctions. -/
def moduleUnboundedOpenTriple :
    Adjunction.Triple (moduleUnboundedDerivedLowerShriek j Λ)
      (moduleUnboundedDerivedInverseImage Λ j) (moduleUnboundedDerivedDirectImage Λ j) where
  adj₁ := moduleUnboundedDerivedLowerShriekAdjunction j Λ
  adj₂ := moduleUnboundedDerivedAdjunction Λ j

/-- Mathlib's original outer-adjoint map, not a bounded-below transport. -/
abbrev moduleUnboundedLowerShriekToDirectImage :=
  (moduleUnboundedOpenTriple Λ j).leftToRight
end AlgebraicGeometry.Scheme.EtaleCohomology
