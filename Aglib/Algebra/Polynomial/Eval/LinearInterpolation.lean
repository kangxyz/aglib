/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Linear interpolation at zero and one


Source: `R5Lab.Aglib.Algebra.Polynomial.Eval.LinearInterpolation`.
Packet SHA-256:
`b218c145d41390c3c42e9b57720736bbdf757b5f8669774a8dd70cd181c034aa`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

noncomputable section
open Polynomial
universe u

namespace Polynomial

variable (k : Type u) [Field k]

/-- Prescribe arbitrary values at the two distinct points 0 and 1. -/
def linearInterpolate (a b : k) : k[X] := C a * (1 - X) + C b * X

@[simp] theorem linearInterpolate_zero (a b : k) : (linearInterpolate k a b).eval 0 = a := by
  simp [linearInterpolate]
@[simp] theorem linearInterpolate_one (a b : k) : (linearInterpolate k a b).eval 1 = b := by
  simp [linearInterpolate]

end Polynomial
