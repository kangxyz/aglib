# Tsen's theorem

This family develops the C₁ property for algebraic extensions of a rational
function field over an algebraically closed field, starting with the finite case. It uses native multivariate polynomials,
finite-dimensional bases and rational functions. Separability of the finite
extension is not assumed.

## Interface and proof structure

- [Basic](Basic.lean) owns the sole `Field.IsC1` definition: a positive-degree homogeneous
  polynomial in `n` variables over a field has a nonzero zero when its degree is
  less than `n`. This definition alone is not Tsen's theorem.
- [HomogeneousZeros](HomogeneousZeros.lean) constructs a chain of prime kernels by successively setting
  variables to zero. The origin ideal has height at least the variable count.
  Nullstellensatz and Krull's height theorem then give a nonzero common zero for
  fewer equations than variables when every equation vanishes at the origin.
- [AlgebraicallyClosed](AlgebraicallyClosed.lean) specializes this result to positive-degree homogeneous
  systems, and proves the C₁ condition for an algebraically closed field itself.
- [Coefficients](Coefficients.lean) uses the existing additive map on polynomial coefficients.
  Linear coordinate maps preserve homogeneous degree and commute with evaluation
  at points over the scalar field; multiplicativity is not required.
- [PolynomialCoordinates](PolynomialCoordinates.lean) proves injectivity and nonzero preservation for the
  bounded polynomial ansatz in a rational-function-field basis. It also exposes
  the native finite-family denominator-clearing theorem in polynomial notation.
- [PolynomialDegree](PolynomialDegree.lean) proves the bound `D + d * m` for evaluation of a degree-`d`
  form with coefficient degrees at most `D` at coordinates of degrees at most `m`.
- [PolynomialSystem](PolynomialSystem.lean) treats `r` homogeneous equations in `n > r*d` variables over
  `K[T]`. It chooses `m = r*(D+1)`: the `n*(m+1)` scalar parameters outnumber the
  `r*(D+d*m+1)` coefficient equations. All coefficients outside this exact bound
  vanish by the degree estimate.
- [RationalFunctionSystem](RationalFunctionSystem.lean) clears the coefficients of all equations with one
  nonzero polynomial denominator and transports the nonzero polynomial solution
  back to the rational function field.
- [FiniteFunctionField](FiniteFunctionField.lean) expands a form over a finite extension in a finite basis.
  For basis size `r`, the resulting `r` equations in `n*r` variables have the same
  degree `d`. Basis independence preserves nonzeroness of the resulting solution.
  The endpoint is `Field.isC1_finite_ratFunc`.
- [AlgebraicFunctionField](AlgebraicFunctionField.lean) descends the finite coefficient set of one form to
  a finite intermediate field, giving the algebraic-extension endpoint
  `Field.isC1_algebraic_ratFunc`.

The field theorem does not itself assert central-simple-algebra splitting,
Brauer-group vanishing, étale cohomological dimension, or curve cohomology. Those
are distinct consumers with additional mathematical proofs.

No assumed Tsen, Brauer-vanishing or cohomological-dimension predicate is used
as an endpoint hypothesis.
