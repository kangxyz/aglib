# Actual Case-II children and their original residue maps

This module proves the local repeated-prime argument on a literal saturated
ordinary blowup chart. Its consumer is the cubic and repeated-root step of
the Case-II continuation. All local conditions below remain explicit.

`original_cubic_sq_dvd_of_caseII_child` starts with an actual equation in
the original local ring `A`. It divides that equation in the native saturated
chart `S = A[m/t]`. The reduced exceptional quotient is a surjective map
`red : S → k[U]` with its actual kernel `(t,z/t)`, its original coefficient
formula, and `red(s/t)=U`. The child is the literal localization at
`P = red⁻¹((q))`. Its three cotangent variables are the actual localized
elements `Q,z/t,t`, where `red(Q)=q`.

The child inputs are dimension two, singularity, and the exact Case-II kernel
of its canonical `Ideal.cotangentPolynomialMap`: the principal ideal of the
square of a homogeneous linear polynomial over the child's actual residue
field. `doubleLineChildCotangentKernel` names this literal kernel with its
residue-field carrier fixed. This is an actual tangent-cone presentation. It is not a tangent-rank
condition, repeatedness premise, marking, or presentation of the local ring
as an ambient hypersurface.

The prime equation `P=(t,z/t,Q)` is derived from the quotient. Singularity
first forces the cubic to vanish modulo `q`. If `h=q*r`, surjectivity of
`red` lifts `r` to an actual chart element `R`. The difference `H-Q*R` belongs
to `(t,z/t)`, giving the exact local relation

```
v² + t*(R*Q + d*v + e*t) = 0.
```

Its quadratic polynomial belongs to the canonical child kernel. Homogeneous
degrees make it a scalar linear square. Regarding it as a polynomial in
`Q`, its degree is at most one, so its linear coefficient must vanish. Thus
`R` lies in the actual child maximal ideal, which says `q | r`; consequently
`q² | h`. The argument uses `q` itself as the local parameter and works for
inseparable closed points and in characteristic two.

`reesAlgebra.reducedDoubleLineChartMap` constructs the required `red` from
the original associated-graded presentation by the native exceptional-chart
equivalence and reduction of the double line. Its surjectivity, exact kernel,
and original coefficient and fraction formulas are proved here. The original
presentation must retain the displayed `t,s,z` symbols and coefficient map;
the two `t,z` formulas alone do not specify the `s` and coefficient formulas.

`original_child_prime_and_residue_of_sq_dvd` consumes this proved divisibility
and the nonzero original cubic supplied by `DoubleLine`. It proves that a
monic irreducible `q` has degree one, constructs `α` with `q=X-α`, identifies
the same actual prime with the kernel of the original evaluation point, and
proves bijectivity of the original localized coefficient map's residue map.
No residue-field section or coefficient field is chosen.

`original_child_prime_eq_displayed_span` identifies that same prime as
`(t,s/t-α̃,z/t)` for any original lift `α̃` of the proved root. This supplies
the exact prime equation consumed by `localizedChart_parameter_not_mem_sq`;
it does not assert persistence of the cubic marker.

The family is symmetric in the two parent tangent-plane generators: applying
the same theorems with the denominator and other generator exchanged is the
second projective chart. Its own native quotient and original symbol formulas
are required; this file makes no global assertion that one affine chart covers
the projective line.

Normality of the actual ordinary chart is used by `DoubleLine` to produce
the nonzero cubic. This file does not prove that geometric normality supplier,
the parent or child Case-II tangent-cone supplier, the persistent simple-root
marker, two-step triple-root entry, or global resolution. The corrected marker
`M(t)` and both retractions of the old unconditional special-form claims remain
in force.
