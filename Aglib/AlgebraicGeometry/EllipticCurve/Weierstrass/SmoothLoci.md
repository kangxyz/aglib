# The actual smooth charts of a Weierstrass cubic

`SmoothLoci` uses the existing native affine coordinate ring and monic infinity
chart of the same projective cubic. The two-variable equation presentations
are explicitly isomorphic to those rings; they supply concrete naive
presentations for the chosen Jacobian localizations.

`affineJacobian W i` is the actual partial derivative selected by `i : Fin 2`.
`affineJacobian_zero` and `affineJacobian_one` identify it with the displayed
Weierstrass gradient formulas. `affineSmoothChart W i` is the literal spectrum
of that localization included through the existing affine chart.
`affineSmoothChart_smoothOne` proves smoothness of relative dimension one over
the original coefficient spectrum. `affineChart_mem_smoothChart_iff` identifies
its range on every affine prime, not only rational points.

The analogous infinity presentation selects the derivative in `v=Z/Y`.
Its Jacobian evaluates to `-1` on the entire original infinity section.
`infinitySmoothChart`, `infinitySmoothOpen`, and their smoothness statements use
the specified localization, with the original section and structure triangles.
`affine_or_smoothInfinity` proves that every projective point is in the actual
affine chart or this smaller smooth infinity chart, over any commutative ring.

`affine_singular_unique` holds over any domain, including characteristics two
and three; its proof divides by neither integer. Over a field with a specified
rational singular solution, `affine_singular_prime_eq` and
`affine_singular_point_iff` identify every prime containing both gradients with
the same evaluation kernel. Existence of that singular solution remains an
explicit hypothesis. `affineSingularPoint` abbreviates the value of the existing
`affinePointOver` at the field's closed point; it does not use the type of
nonsingular coordinate points.

The source is the full reusable `PointedResolution.Weierstrass.SmoothLoci`
body, plus only the general-ring infinity-cover section of `DVRNode:312–425`.
No DVR guard, geometry-family input, representability, model marking or purity
claim is introduced. Actual strict-transform/DVR consumers keep their own
regularity, dimension and descent hypotheses.
