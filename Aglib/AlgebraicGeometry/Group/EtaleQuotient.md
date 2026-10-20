# Comparisons of given etale group quotients

`EtaleQuotient.lean` starts with actual group morphisms and the original
all-field `Curve.Properties`. A kernel inclusion on points over a specified
algebraically closed extension yields an all-test cocycle. Native effective
morphism descent then constructs the actual quotient comparison and its
factorization and pointedness equations. Equality of the actual point kernels
for two given etale surjections yields a scheme isomorphism and, by the native
proper-curve pointed-morphism theorem, a group isomorphism.

The underlying kernel pair in `Morphisms/Etale/KernelPair.lean` is literally the
native scheme pullback with its original two projections and lift. Its smooth
structure morphism is geometrically reduced at every field base change, using
`Geometrically/Reduced/Smooth.lean`. The fixed-extension point detection theorem
retains the geometrically reduced locally finite-type source and separated
locally finite-type target.

`MultiplicationTransport.lean` transfers literal multiplication along an actual
group isomorphism; `Finite/GeometricDegreeOperations.lean` proves the positive
geometric-fibre-cardinality composition and isomorphism formulas on the actual
point fibres. The decomposition reuses the native sigma-fibre equivalence and
records the original intermediate and source points.

`CurveIsogeny.lean` obtains finiteness of a dominant map from the existing
proper dimension-one criterion and the actual curve conditions. Its pointed
finite-etale packaging still takes the exact universal characteristic-zero
finite-surjective group-homomorphism etaleness statement as an input. The module
does not prove that family. It imports no marked isogeny, Tate presentation,
model-existence record, or analytic uniformization.
