/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.RingTheory.Etale.QuadraticRoot

/-!
# Derivative invertibility and maximal-ideal membership of the chosen quadratic root

Source: R5 baseline `e6d63abca2403f50b6b413101ad7f6a7f2e0e2c7`.
Existing declarations, chosen maps and explicit evidence boundaries are preserved.
-/

/-!
## Migration source

Native extraction from `lean/R5Lab/Aglib/RingTheory/Etale/QuadraticDerivative.lean` at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`59137eafec4a5b831283986b72daab81f1955e0fcdbafa4898de6c4933b01cfc`.
-/

@[expose] public section

noncomputable section
open Polynomial IsLocalRing
universe u

namespace Algebra.QuadraticRoot

variable {R : Type u} [CommRing R]

/-- The nonmonic quadratic derivative is already a unit in the actual
standard étale algebra: the extra denominator is the chosen monic root. -/
theorem root_derivative_isUnit (a b c : R) :
    IsUnit (2 * algebraMap R _ a * Algebra.QuadraticRoot.root a b c +
      algebraMap R _ b) := by
  let z := (Algebra.QuadraticRoot.pair a b c).X
  let v := Algebra.QuadraticRoot.generatorUnit a b c
  have hv : (v : Algebra.QuadraticRoot.RootAlgebra a b c) = z :=
    (Algebra.QuadraticRoot.generator_isUnit a b c).unit_spec
  have hz := (Algebra.QuadraticRoot.pair a b c).hasMap_X.1
  change aeval z (Algebra.QuadraticRoot.polynomial a b c) = 0 at hz
  simp only [Algebra.QuadraticRoot.polynomial, map_add, map_sub, map_pow, map_mul,
    aeval_X, aeval_C] at hz
  have hd := (Algebra.QuadraticRoot.pair a b c).hasMap_X.isUnit_derivative_f
  change IsUnit (aeval z (Algebra.QuadraticRoot.polynomial a b c).derivative) at hd
  have he : aeval z (Algebra.QuadraticRoot.polynomial a b c).derivative =
      2 * z - algebraMap R _ b := by
    simp [Algebra.QuadraticRoot.polynomial, derivative_pow, derivative_mul, map_ofNat]
  rw [he] at hd
  have heq : 2 * algebraMap R _ a * Algebra.QuadraticRoot.root a b c +
      algebraMap R _ b = 2 * z - algebraMap R _ b := by
    have hi := v.mul_inv
    change (v : Algebra.QuadraticRoot.RootAlgebra a b c) * ↑v⁻¹ = 1 at hi
    rw [← hv] at hz ⊢
    dsimp [Algebra.QuadraticRoot.root]
    change 2 * algebraMap R (Algebra.QuadraticRoot.RootAlgebra a b c) a *
      (-algebraMap R _ c * (↑v⁻¹ : Algebra.QuadraticRoot.RootAlgebra a b c)) +
      algebraMap R _ b = 2 * (v : Algebra.QuadraticRoot.RootAlgebra a b c) - algebraMap R _ b
    linear_combination -2 * (↑v⁻¹ : Algebra.QuadraticRoot.RootAlgebra a b c) * hz +
      (2 * (v : Algebra.QuadraticRoot.RootAlgebra a b c) - 2 * algebraMap R _ b) * hi
  exact heq ▸ hd

/-- The chosen quadratic root lies in the actual extension of the original
maximal ideal, not merely in the kernel of one selected residue point. -/
theorem root_mem_extended_maximalIdeal [IsLocalRing R] (a b c : R)
    (hc : c ∈ maximalIdeal R) :
    Algebra.QuadraticRoot.root a b c ∈
      Ideal.map (algebraMap R (Algebra.QuadraticRoot.RootAlgebra a b c)) (maximalIdeal R) := by
  let I := Ideal.map (algebraMap R (Algebra.QuadraticRoot.RootAlgebra a b c)) (maximalIdeal R)
  exact I.mul_mem_right _ (I.neg_mem (Ideal.mem_map_of_mem _ hc))

end Algebra.QuadraticRoot
