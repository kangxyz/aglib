/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.ZeroModule

/-! Focused consumer of the vanishing criterion for Hilbert polynomials: a coherent module on
projective space over a field has zero Hilbert polynomial exactly when it is zero, with axiom
guards. -/

@[expose] public section

open CategoryTheory Limits AlgebraicGeometry AlgebraicGeometry.Scheme.Cohomology
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

example (k : Type u) [Field k] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace k ι).Modules) (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F) :
    projectiveHilbertPolynomial k ι F = 0 ↔ IsZero F :=
  projectiveHilbertPolynomial_eq_zero_iff k ι n e hF

/-- A nonzero coherent module has nonzero Hilbert polynomial. -/
example (k : Type u) [Field k] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace k ι).Modules) (hF : affineLocallyFiniteType (ProjectiveSpace k ι) F)
    (hF0 : ¬IsZero F) : projectiveHilbertPolynomial k ι F ≠ 0 :=
  fun h => hF0 (isZero_of_projectiveHilbertPolynomial_eq_zero k ι n e hF h)

/--
info: 'AlgebraicGeometry.Scheme.Cohomology.projectiveHilbertPolynomial_eq_zero_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms AlgebraicGeometry.Scheme.Cohomology.projectiveHilbertPolynomial_eq_zero_iff
