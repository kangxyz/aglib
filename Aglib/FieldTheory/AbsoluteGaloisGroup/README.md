# Restriction in algebraic towers

`RestrictScalars.lean` proves continuity of the actual `AlgEquiv.restrictScalarsHom`
for the Krull topologies, assuming algebraicity of the top field over the
intermediate field. `closureRestriction` is the same map on the chosen closure.

The algebra-homomorphism view of the existing geometrically chosen closure
embedding is in
[`ClosureAlgHom`](../../AlgebraicGeometry/FundamentalGroup/Field/ClosureAlgHom.lean).
It follows that actual map; it supplies no independence from its choice.
