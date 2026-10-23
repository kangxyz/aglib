# The original comparison graph

[ProjectiveDomination.lean](ProjectiveDomination.lean), in
`AlgebraicGeometry.Scheme.Birational`, constructs `comparisonGraph` for
the exact maps `β : Y ⟶ Z`, `π : W ⟶ Z`, `a : Y ⟶ W` and the supplied
equation `a ≫ π = β`.

The target is the literal pullback `Y ×[Z] W`. Its two projection equations
are the identity of the original `Y` and the original `a`.
`comparisonGraph_isClosedImmersion` proves closedness from separation of
`π`, using Mathlib's actual graph theorem. No regularity, dimension or
Noetherianity is needed for this graph step.

This is the graph part of the projective-domination argument in
[Stacks 0C4Q](https://stacks.math.columbia.edu/tag/0C4Q). The source contains
no projectivity oracle or hypothesis packaging the desired surface
conclusion. The projective embedding of the pullback, its construction
along the original point-blowup chain and the final standard embedding of
the original `Y` remain separate obligations.
