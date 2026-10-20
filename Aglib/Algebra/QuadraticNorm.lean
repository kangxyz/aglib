/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Tactic.Ring

/-!
# Coordinate formulas for the canonical quadratic algebra norm

The source norm and pair multiplication reuse `QuadraticAlgebra R (-δ) 0`
and its norm homomorphism. The two specialized integer identities remain
downstream consequences of the coordinate law.

Source: `R5Lab.Aglib.Algebra.QuadraticNorm`.
Packet SHA-256:
`58eb4eacc9b5f99810a3e37b96e089a70540a381d30348c17ff36a039db407af`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

namespace QuadraticAlgebra

variable {R : Type*} [CommRing R]

/-- The source coordinate norm is the norm in the existing quadratic algebra. -/
theorem norm_mk_neg (δ a b : R) :
    norm (⟨a, b⟩ : QuadraticAlgebra R (-δ) 0) = a ^ 2 + δ * b ^ 2 := by
  simp [norm_def, pow_two]
  ring

/-- The source pair multiplication is multiplication in the existing quadratic algebra. -/
theorem mk_mul_mk_neg (δ a b c d : R) :
    (⟨a, b⟩ : QuadraticAlgebra R (-δ) 0) * ⟨c, d⟩ =
      ⟨a * c - δ * b * d, a * d + b * c⟩ := by
  ext <;> simp
  ring

/-- The literal coordinate norm law for a symbol with square `-δ`. -/
theorem norm_mul_coordinates (δ a b c d : R) :
    (a * c - δ * b * d) ^ 2 + δ * (a * d + b * c) ^ 2 =
      (a ^ 2 + δ * b ^ 2) * (c ^ 2 + δ * d ^ 2) := by
  ring

end QuadraticAlgebra
