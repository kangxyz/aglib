# Coefficient base change and residue fibres

`BaseChange` constructs `WeierstrassCurve.Projective.coefficientSchemeMap W f`
on the existing literal projective Weierstrass cubic for an arbitrary
commutative-ring homomorphism. The homogeneous quotient map sends each
coordinate to the same coordinate and each scalar to its image under `f`.
The standard homogeneous-localization chart maps are explicit.

`coefficientBaseChangeIso` identifies the coefficient cubic with the actual
pullback of `structureMap W` along `Spec.map (algebraMap R S)`.
Its first projection is the original coefficient morphism, its second is the
coefficient cubic's structure map, and `coefficientBaseChangeIso_hom` identifies
the entire forward map with that canonical pullback lift. The infinity section
has the original pointed pullback equation.

`InfinityChart` supplies the monic cubic presentation of the same coordinate-one
chart and the actual overlap `(u,v)=(x/y,1/y)`, with inverse
`(x,y)=(u/v,1/v)`. The existing native affine coordinate ring, coordinates,
lift, and coefficient tensor equivalence are reused. The two charts prove
flatness over an arbitrary commutative ring.

`Integrality.scheme_isIntegral_of_isDomain` proves integrality of the same
projective cubic over every domain, including singular equations. The proof
embeds the monic infinity ring in its overlap with the native affine domain;
no discriminant, nonsingular-geometry, or normal-component family is assumed.
The older conditional `GeometryInputs.scheme_isIntegral` API remains separate.

`ResidueFiber.specialFibre W` is an abbreviation of the shared
`Scheme.LocalRing.ResidueFiber.obj (structureMap W)` literal residue pullback.
`specialCoefficientIso` identifies it with the coefficient-reduced equation;
both projection equations and its integrality over every local coefficient
ring are proved by the same base-change and domain theorems.

The source selection is the mathematical coefficient/chart and unconditional
integrality API plus `PointedResolution.Weierstrass.Surface:100–123`.
Marked models, geometry-background records, minimality, regular-model assembly
and representability are outside these leaves.
