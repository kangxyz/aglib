# Cross-curve pullback of degree-zero classes

`degreeZeroCurvePullback` is the additive map between the existing
normalized degree-zero Picard groups of two actual pointed curves. Its
underlying value is pullback along the literal first-coordinate map
`f ▷ T : X ⊗ T → Y ⊗ T`. The hypotheses are actual curve properties,
preservation of the chosen origins, and finite etale surjectivity of `f`.
Every test scheme and every structural geometric field map are retained.

`degreeZeroCurvePullback_naturality` proves compatibility with every map of
test schemes. `fibreDegree_curvePullback` proves the exact multiplier `n`
on every geometric fibre when the input is the actual
`HasGeometricDegree f n`. The zero-degree preservation theorem uses the
existing finite-flat rank and native curve-degree pullback formulas.
All previously named geometry, norm/order and product-formula families
are instantiated by their native proved suppliers.

The current consumer is `Group/DualIsogeny.lean`. No representing scheme,
Picard representability premise, new degree function, or generic-family
conclusion is introduced.
