# Lifts of actual line bundles

`TranslationLift.lean` uses the native pullback pseudofunctor of module
sheaves and Mathlib's `CoGrothendieck` category. A lift is an automorphism of
the original scheme together with its original line bundle. `baseHom` is
the actual forgetful map to scheme automorphisms.

`vertical_eq_scalar` uses the proved fact that every endomorphism of a
locally rank-one module sheaf is multiplication by a global function.
`commute_vertical` combines that fact with the actual pullback of scalar
multiplication: a lift fixing global functions commutes with every lift
over the identity. `commute_of_base_eq_pow` then proves that such a lift
commutes with any lift whose base automorphism is a power of its own.

`cancelFrame` uses the canonical tensor-pullback map and unit map to cancel
a framed line bundle while retaining an unframed factor. It is injective
because tensoring by an invertible module is an equivalence.
`cancelFrame_pullback` proves its actual pullback compatibility.

`ActualPullback.canonicalDeck` is defined by the Cartesian universal
property and preserves the original pullback projection. `frameLift` is
defined through the same projections, so its required factorization is
part of its construction. The Hom-restriction identity is proved for an
arbitrary pullback pseudofunctor and then specialized to the actual module
sheaves. Cartesian uniqueness converts commutation of lifts into
equivariance of the tensor-cancellation map, and injectivity recovers
invariance of the original frame.

The resulting `frame_fixed_of_deck_power` applies to a scheme map `p`,
source and target automorphisms in an actual commuting square, an actual
ratio-bundle isomorphism, a frame of its pullback, and a deck automorphism
which is a power of the source automorphism. The source automorphism must
fix global functions. These are the explicit hypotheses; no alternation
identity is supplied as a premise.

The current consumer
[`Group/WeilPairing.lean`](../Group/WeilPairing.lean) supplies actual
translations, the identity ideal, and the exact frame of the positive point
class. Proper-curve constants supply the global-function condition.
The argument does not divide by the exponent or by two.
