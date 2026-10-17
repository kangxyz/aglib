/-
Copyright (c) 2026 Algebraic geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Grassmannian.BaseChange
import all Mathlib.RingTheory.Grassmannian

/-!
# The base-change formula instance for Mathlib's Grassmannian

This file supplies `Module.Grassmannian.BaseChangeMkQFormula R M` for every commutative ring `R`
and module `M`. Importing it makes every result stated under that premise unconditional.

Mathlib does not expose the body of `Module.Grassmannian.baseChangeMkQ`, so this is the only
Aglib source that reads it, through `import all Mathlib.RingTheory.Grassmannian`. That import is a
documented one-file exception to the public-import policy in `scripts/check_library_layout.py`.
Delete this file and the exception once Mathlib exposes `baseChangeMkQ` (`@[expose]`) or
publishes a lemma `baseChangeMkQ_tmul`; the instance can then be proved from the public API.
-/

@[expose] public section

universe u v w

open TensorProduct

namespace Module.Grassmannian

/-- Mathlib's `baseChangeMkQ` satisfies the component formula
`baseChangeMkQ B N (b ⊗ m) = b ⊗ [1 ⊗ m]`, read off its definition. -/
instance baseChangeMkQFormula (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M]
    [Module R M] : BaseChangeMkQFormula.{u, v, w} R M where
  baseChangeMkQ_tmul N b m := by
    simp [baseChangeMkQ, AlgebraTensorModule.cancelBaseChange_symm_tmul]

end Module.Grassmannian
