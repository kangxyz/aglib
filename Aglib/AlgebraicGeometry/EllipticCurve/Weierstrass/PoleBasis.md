# Intrinsic small-degree coordinates

[PoleBasis.lean](PoleBasis.lean) works over every field, on Mathlib's literal
`W.toAffine.CoordinateRing`. It requires neither nonsingularity nor a supplied
pole-order or classification theorem.

For a nonzero element, `affineColength_eq_normDegree` identifies the dimension
of its actual principal-ideal quotient with the degree of its quadratic
algebra norm. `affineAlgEquiv_normDegree` transports that quotient through an
actual base-field algebra isomorphism. The native norm formula for
`p(x) + q(x)y` has degree `max (2 deg p, 2 deg q + 3)`; the distinct parities
prevent cancellation of the two largest terms.

The degree bounds put elements of norm degree at most two in the span of
`1, x`, and elements of norm degree at most three in the span of `1, x, y`.
In particular, `affineAlgEquiv_coordinateForms` proves that an
actual affine algebra isomorphism sends `x` to `a x + r` and `y` to
`b y + s x + t`. This is the lower input to the arbitrary pointed-isomorphism
comparison in [PointedIsomorphism.lean](PointedIsomorphism.lean). Leading
coefficient relations and j-invariance belong to that consumer.
