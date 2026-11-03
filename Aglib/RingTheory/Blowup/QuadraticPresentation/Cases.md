# Fixed-coordinate quadratic case bridge

## Imports and ownership

The new lower leaf is `Aglib.RingTheory.Blowup.QuadraticPresentation.Cases`.
Its precise imports are the existing `QuadraticPresentation` and Mathlib's
finite linear-combination supplier. It does not modify either owner and does
not construct a second cone, chart, polynomial equivalence, or coefficient map.

## Exact public mathematical scope

Fix any `k : Type u` with `Field k`, and the existing
`MvPolynomial.FirstCoordinate.dehom` from three original variables to two.

1. For `p q : MvPolynomial (Fin 3) k`, both homogeneous of degree two,
   `dehom p = dehom q` implies `p = q`. Expand each in the existing six
   original exponents and use `dehom_quadratic_coeff`. The expansion is a
   private coefficient enumeration, not a new polynomial representation.
2. For `q` homogeneous of degree two and `q ≠ 0`, prove the equivalence

   `(∃ c : k, c ≠ 0 ∧ ∃ l : MvPolynomial (Fin 2) k,
      l.totalDegree ≤ 1 ∧ dehom q = C c * l^2)`

   iff

   `(∃ c : k, c ≠ 0 ∧ ∃ L : MvPolynomial (Fin 3) k,
      L.IsHomogeneous 1 ∧ L ≠ 0 ∧ q = C c * L^2)`.

   The forward direction derives the affine linear expansion from the
   existing six-coefficient `QuadraticClosedPoint.eq_quadratic_of_totalDegree_le`,
   whose degree-two coefficients vanish. Its three literal coefficients give
   the homogeneous linear form. Fixed-degree injectivity proves the equation;
   `L ≠ 0` follows from original `q ≠ 0`. Reverse direction uses stock
   `homogeneousSubmodule_one_eq_span_X` and finite span coefficients to bound
   the actual dehomogenized line. No root or enlarged field is chosen.
3. Conclude the honest dichotomy: either the exact Case-I affine predicate
   fails to be a nonzero scalar linear square, or there is an actual nonzero
   homogeneous linear `L` with `Ideal.span {q} = Ideal.span {L^2}`.
   Remove the scalar only at the ideal level using
   `Ideal.span_singleton_mul_left_unit` applied to `C c`.

## Boundaries

This is the missing fixed-coordinate classification bridge, not a source of
Hilbert numerics, canonical generation, Gorenstein preservation, actual markers,
or termination. The genuine full-kernel equality is supplied by the accepted
Hilbert producer and remains the original canonical map. Geometric consumers
must preserve it when selecting either branch. All characteristics and all
fields are retained; no ADE or quadratic-form normal-form classification occurs.
