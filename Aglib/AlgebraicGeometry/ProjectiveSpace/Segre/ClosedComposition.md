# Actual closed composition through the binary Segre embedding

Let `a : W → Spec R`, let `j : W → ProjectiveSpace R κ` be a closed
immersion with its actual triangle `j ≫ toSpec R κ = a`, and let
`h : Y → pullback a (toSpec R ι)` be a closed immersion. The map
`ProjectiveSpace.Segre.closedCompositionMap` is the original composite
from this unchanged source to `ProjectiveSpace R (ι × κ)`.

Its intermediate `baseEmbeddingProductMap` first swaps the two factors
of the original pullback, then applies the native `pullback.map` induced
by the identity on `ProjectiveSpace R ι` and the given map `j`.
Its projections are proved to be exactly the original projective
projection and the original base projection followed by `j`.
The original binary `Segre.embedding R ι κ` then supplies the final map.
Closedness follows from native base-change and composition results.

`closedCompositionMap_toSpec` proves that the resulting structure map is
exactly `h ≫ pullback.fst a (toSpec R ι) ≫ a`. Coordinate reindexing uses
the existing `ProjectiveSpace.reindexIso`, with the same original
coefficient triangle recorded by `closedCompositionMap_reindex_toSpec`.
There is no projectivity existence input or replacement structure map.

The construction and projection identities have no finiteness or
nonemptiness hypotheses on the coordinate types. For finite coordinate
types, `exists_finite_reindex_closedCompositionMap` reindexes to
`ULift (Fin n)`, including `n = 0`. Empty indices and empty sources are
therefore included in the general result.

When a consumer needs the standard positive coordinate form,
`exists_positive_reindex_closedCompositionMap` assumes only that the
actual source `Y` is nonempty, in addition to the given closed maps
and finite indices. The actual map from `Y` and the original coordinate
open cover prove `Nonempty (ι × κ)`. The result then reindexes to
`ULift (Fin (n + 1))`. A nonempty integral-surface consumer can supply
this source condition directly; neither index set is assumed nonempty
as an additional global condition.

Input basis: Aglib `8b93cc5940dc93f39a2eaf05e6985af28250a578`,
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean `4.34.1`.
The source reuses `Segre/ClosedImmersion`, its `FiniteProduct` owner,
the native pullback-map property theorem, and `ProjectiveSpace/Reindex`.
The contraction author's affine row construction and the global
contraction induction remain separate consumers.
