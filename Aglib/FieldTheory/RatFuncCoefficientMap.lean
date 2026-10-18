/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.PolynomialResidueBaseChange
public import Aglib.FieldTheory.RatFuncInversion

/-!
# Coefficient extension and inversion of actual rational functions

The coefficient map already used for polynomial local residues fixes the
variable, extends the coefficient-field homomorphism, and commutes with the
actual substitution automorphism `X ↦ X⁻¹`.
-/

@[expose] public noncomputable section

namespace Polynomial.LocalResidue

variable {k L : Type*} [Field k] [Field L] (φ : k →+* L)

/-- The actual rational-function coefficient map extends the original field map. -/
@[simp]
theorem fractionMap_C (a : k) :
    fractionMap φ (RatFunc.C a) = RatFunc.C (φ a) := by
  simpa only [Polynomial.map_C, RatFunc.algebraMap_C] using fractionMap_polynomial φ (C a)

/-- The coefficient map preserves the actual rational-function variable. -/
@[simp]
theorem fractionMap_X : fractionMap φ (RatFunc.X : RatFunc k) = RatFunc.X := by
  simpa only [Polynomial.map_X, RatFunc.algebraMap_X] using fractionMap_polynomial φ X

private theorem fractionMap_inversion_polynomial (p : k[X]) :
    fractionMap φ (RatFunc.inversion k (algebraMap k[X] (RatFunc k) p)) =
      RatFunc.inversion L (fractionMap φ (algebraMap k[X] (RatFunc k) p)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n a => simp

/-- Actual coefficient extension commutes with actual inversion on every rational function. -/
theorem fractionMap_inversion (x : RatFunc k) :
    fractionMap φ (RatFunc.inversion k x) = RatFunc.inversion L (fractionMap φ x) := by
  induction x using RatFunc.induction_on with
  | f p q _ => simp only [map_div₀, fractionMap_inversion_polynomial]

/-- The inversion square as equality of the original field homomorphisms. -/
theorem fractionMap_comp_inversion :
    (fractionMap φ).comp (RatFunc.inversion k).toRingHom =
      (RatFunc.inversion L).toRingHom.comp (fractionMap φ) := by
  ext x
  exact fractionMap_inversion φ x

end Polynomial.LocalResidue
