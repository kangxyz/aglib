/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.TransferInstance

/-!
# Typed multiplication transport for canonical Rees cohomology

The native transported module action is compared at variable additive modules.
Concrete cohomology consumers supply only their canonical additive equivalence
and its actual multiplication square; they do not unfold derived carriers or
compare the linear and additive presentations at concrete coefficients.
-/

@[expose] public section

namespace LinearEquiv

variable {A B M N : Type*} [Semiring A] [Semiring B]
  [AddCommMonoid M] [AddCommMonoid N] [Module A M] [Module A N] [Module B N]

/-- An actual multiplication equation across an additive equivalence determines
the native transported module action, with the same constructor on both sides. -/
theorem module_smul_eq_of_apply_eq (e : M ≃ₗ[A] N) (b : B) (x y : M)
    (h : e y = b • e x) :
    letI := e.toAddEquiv.module B
    b • x = y := by
  let := e.toAddEquiv.module B
  apply (e.toAddEquiv.linearEquiv B).injective
  exact ((e.toAddEquiv.linearEquiv B).map_smul b x).trans h.symm

end LinearEquiv
