/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Finite presentation of the native module cokernel

The original categorical cokernel of a map from a finite module to a
finitely presented module is finitely presented. Its native range-quotient
comparison transfers the ordinary finite-presentation theorem without a
Noetherian assumption. Ring and module universes remain independent.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

universe u v

variable {R : Type u} [Ring R] {M N : ModuleCat.{v} R}

/-- A finite source and finitely presented target give finite presentation of the
unchanged native categorical cokernel. -/
theorem finitePresentation_cokernel (f : M ⟶ N)
    [Module.Finite R M] [Module.FinitePresentation R N] :
    Module.FinitePresentation R (cokernel f : ModuleCat.{v} R) := by
  let : Module.FinitePresentation R (N ⧸ f.hom.range) :=
    Module.finitePresentation_of_surjective f.hom.range.mkQ
      (Submodule.mkQ_surjective _) (by
        rw [Submodule.ker_mkQ]
        exact Submodule.fg_range f.hom)
  exact Module.FinitePresentation.of_equiv
    (cokernelIsoRangeQuotient f).symm.toLinearEquiv

end ModuleCat
