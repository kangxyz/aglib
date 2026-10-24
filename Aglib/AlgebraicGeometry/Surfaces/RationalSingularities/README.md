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
modification rings and Gorenstein reduction retain their separate hypotheses.
The ordinary rational-blowup interfaces below assume Nagata explicitly.

The full resolution criterion RES and its quasi-excellent corollary
RES-QE remain open. The universal vanishing result and ordinary rational-blowup
interfaces below are prerequisites for that construction.

## Ordinary rational blowups and the full exceptional fibre

[Blowup](Blowup.md) constructs the literal normalized ordinary maximal-ideal
blowup and its ideal pullback. [IdealPowers](Blowup/IdealPowers.md) proves
vanishing and original section images for its actual ideal powers;
[Normality](Blowup/Normality.md) proves that the normalization map is an
isomorphism, hence normality of the ordinary blowup. The hypotheses are a
normal Noetherian Nagata local domain of dimension two and the genuine
`NormalModificationH1Vanishing A` predicate.

[Exceptional](Blowup/Exceptional.md) retains the full exceptional scheme,
including nilpotents, its original residue structure map and coefficient
bijection. [Geometry](Blowup/Exceptional/Geometry.md) gives its actual
projective embedding, positive twist and closed-stalk regular-primary
parameters. [Powers](Blowup/Exceptional/Powers.md) identifies original power
layers with sections and preserves products and degree zero. Here the
positive twist is the original ideal line `L = i*(m O_X)`, and its powers
are restrictions of the original ideal powers. These interfaces serve the
curve and tangent-cone consumers; they do not prove Gorenstein reduction,
full RDP termination or existence of a resolving chain.
