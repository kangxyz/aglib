/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# The C₁ condition

This is the homogeneous-form definition. Zero forms are permitted and degree zero
is excluded. The finite-function-field theorem is a separate mathematical supplier.
-/

@[expose] public section

namespace Field

/-- A field is C₁ if a positive-degree homogeneous form in more variables than its
 degree has a nonzero zero. -/
def IsC1 (K : Type*) [Field K] : Prop :=
  ∀ (n d : ℕ) (p : MvPolynomial (Fin n) K), 0 < d → d < n →
    p.IsHomogeneous d → ∃ x : Fin n → K, x ≠ 0 ∧ MvPolynomial.eval x p = 0

end Field
