# Rationality of the literal normal domain completion

Import `Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.Completion`.
Source: [Completion.lean](Completion.lean).

`Scheme.RationalSingularities.normalModificationH1Vanishing_completion`
starts with a commutative Noetherian local domain `S` of dimension two.
Its literal maximal-adic completion `H` is assumed to satisfy both
`IsDomain H` and `IsIntegrallyClosed H`. The conclusion is

`NormalModificationH1Vanishing S → NormalModificationH1Vanishing H`.

This predicate means vanishing of the existing degree-one `Sheaf.H` of the
structure-module additive sheaf on every integral normal proper dominant
birational model, where birationality uses its original function-field map.
It is not an existence predicate for regular models.
Normality of `S` descends by faithful flatness; it is not an extra input.
The complete-local dimension-two theorem supplies Nagata for `H`.
Nagata of `S` is unnecessary.

For an arbitrary supplied model `Z` over `H`,
[normalized-point domination](../Birational/NormalizedPointDomination/AffineBase.md)
constructs a normal chain terminal `T` dominating `Z`.
[CompletionDescent](../Resolution/CompletionDescent.md) descends only that
chain, with its literal completion comparison and both projection equations.
The lower chain is normal, so the original universal vanishing applies.

The original qcqs flat cohomology tensor map, pullback-unit isomorphism and
structure-module map of the comparison give H1 vanishing on `T`.
The proper-birational H1 injection then gives vanishing on `Z`.
All groups remain the existing `Sheaf.H` of `moduleAddSheaf` in universe
`u + 1`, with the original scalar and pullback maps.

The proof does not algebraize `Z` or require a regular terminal.
Normal-domain completion is a supplied hypothesis and is not derived by
this implication.
