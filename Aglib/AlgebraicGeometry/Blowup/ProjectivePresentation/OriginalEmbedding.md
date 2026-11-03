# A projective embedding of the original blowup

Source: [OriginalEmbedding.lean](OriginalEmbedding.lean).

`ProjectivePresentation.exists_original_projective_embedding` embeds the
SAME `B.Y` of a native blowup datum into finite-coordinate projective space
over the unchanged commutative ring R. Its exact structural equation is

```
k ≫ toSpec R J = B.map ≫ j ≫ toSpec R ι.
```

The input is a locally Noetherian scheme X, an arbitrary ideal sheaf and its
native blowup datum B, and a closed embedding of X into finite-coordinate
projective space over R. No domain, integrality, normality, dimension,
properness, nonempty-coordinate, or Noetherian-base hypothesis is assumed.
The result does not promise nonempty or positive standard coordinates when
the original blowup is empty.

The existing arbitrary-base-change projective presentation is specialized
at the identity of X. The original identity-pullback projection to B.Y is
an isomorphism, and its actual inverse transports that same embedding.
The native pullback equation gives the displayed original blowdown triangle.
No new blowup model or embedding backend is constructed.

This proof body was moved once from the proper normalized-chain embedding
consumer. That consumer now calls this lower theorem; its finite
normalization, finite-map projective embedding and recursion are unchanged.

Direct consumers: [AlgebraicGeometry/Surfaces/Resolution/NormalizedPointBlowupChain/ProjectiveEmbedding](../../Surfaces/Resolution/NormalizedPointBlowupChain/ProjectiveEmbedding.md).
