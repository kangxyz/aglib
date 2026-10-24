# Rational surface singularities

[Regular](Regular.md), in `Scheme.RationalSingularities`, defines
`NormalModificationH1Vanishing A` for a commutative domain. It quantifies over
the original structure-H1 groups of every supplied integral normal scheme
proper and dominant over `Spec A`, with invertible original function-field
map. It does not choose a resolution or restrict the models to projective
ones.

`normalModificationH1Vanishing_of_regularLocal` proves this property for a
regular local ring of dimension two. It derives the domain and regular
spectrum, constructs an actual dominating regular point-blowup chain, and
uses the original cohomology map to inject the given model's H1 into zero.

The required lower results are positive higher-direct-image vanishing for
the [actual regular point blowup](../../Cohomology/Blowup/RegularPoint.md)
and the [original birational H1 injection](../../Cohomology/Proper/BirationalFirstCohomology.md).
The chain argument uses middle exactness and a zero first higher image;
its base ring need not be complete.

This universal vanishing property is broader than the conventional
rational-singularity definition whose domain includes a normal Nagata
local ring. Regularity is not used to assert Nagata. Propagation to local
modification rings, normality of ordinary rational blowups and Gorenstein
reduction are separate obligations.

The full resolution criterion RES and its quasi-excellent corollary
RES-QE remain open; this family presently supplies the universal vanishing
result over an already regular local base.
