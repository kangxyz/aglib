# A quadratic in the square of an actual closed plane point

`MvPolynomial.exists_scalar_linear_sq_of_mem_maximal_sq` takes a field `k`,
an actual maximal ideal `M` of `MvPolynomial (Fin 2) k`, and a polynomial `F`
with `F ≠ 0`, `F.totalDegree ≤ 2`, and `F ∈ M^2`. The residue-degree input is

```
1 < Module.finrank k (MvPolynomial (Fin 2) k ⧸ M).
```

This is the original ideal quotient and its original constant-coefficient
algebra structure. The conclusion gives literal `c : k` and `l` in the original
polynomial ring such that `c ≠ 0`, `l ≠ 0`, `l.totalDegree ≤ 1`, and
`F = C c * l^2`.

The six-coefficient theorem `QuadraticClosedPoint.quadratic_mem_sq` is available
for the actual dehomogenized cone. `eq_quadratic_of_totalDegree_le` constructs
that six-coefficient expansion from the original polynomial; it is not an
extra presentation hypothesis. `QuadraticClosedPoint.linear` uses the original
coordinates, and its total-degree bound is proved.

## The elimination argument

The focused inner result
`Polynomial.QuadraticClosedPoint.monic_quadratic_mem_sq` works in the original
iterated polynomial ring `k[U][V]`. It contracts the actual maximal ideal to
`k[U]`; the native Jacobson contraction theorem makes that ideal maximal.
A monic generator of the reduced ideal in the actual coefficient-quotient
polynomial ring must have degree one, because its square divides the original
monic quadratic. This produces `V-G(U)` in the original ideal.

Monic reduction gives a representative G of degree below the monic contraction
generator f. The original coefficient quotient map is proved onto, and its
canonical algebra equivalence identifies the original residue dimension with
`natDegree f`; thus this degree exceeds one. Evaluation at G maps the original
ideal into `(f)`. Its square condition makes `F(U,G)` divisible by `f^2`, and
ordinary differentiation followed by evaluation makes `∂V F(U,G)` divisible by
f. The strict degree bounds force both to vanish. The exact quadratic identity
then gives `F=(V-G)^2`. Comparing constant V-coefficients proves that G is affine
linear.

Regrouping variables preserves constants. The outer proof normalizes a nonzero
quadratic coefficient by a scalar, a swap, or the invertible shear
`U ↦ U+V`. Each induced quotient equivalence is the canonical one over k.
The coordinate change is undone in the literal square identity. If all three
quadratic coefficients vanish, partial differentiation of the original squared
ideal excludes a nonzero linear coefficient, and properness excludes a
nonzero constant.

No division by two occurs. The result includes characteristic two, imperfect
fields, inseparable closed points and fields of infinite p-rank. It uses no
coefficient-field section, finite-p-rank premise or arbitrary-ideal
strengthening. In particular it does not assume that the child point is rational.

## Sources and consumer boundary

The statement is the maximal-ideal specialization of
[Stacks 54.12.2, tag 0BGD](https://stacks.math.columbia.edu/tag/0BGD).
The source's characteristic-two coefficient-derivation argument is replaced
by the characteristic-free elimination proof above; no nonsquare-detecting
field derivation is an unproved premise.

Source basis: Aglib HEAD `f27c5fa9b8f76147e16caacf52f56f26eabddb87`,
Lean 4.34.1, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Relevant exact Mathlib owners are `Ideal/MonicSpan.lean:27,35`,
`Jacobson/Ring.lean:540`, `Polynomial/Basic.lean:544`, `AdjoinRoot.lean:835`,
`Polynomial/Div.lean:171`, `Polynomial/Degree/Domain.lean:58,71`,
`Polynomial/Degree/SmallDegree.lean:41,45`, and `MvPolynomial/Equiv.lean:649`.

The Case-I saturated chart, original child residue map, and path-marking
assembly remain separate consumers. No global resolution theorem is asserted.
