# Packet 1 source correspondence

Native source: `Aglib/AlgebraicGeometry/Morphisms/FiniteEtale/SplitProjection.lean`.

Frozen source: `R5Lab.Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.SplitProjection`, R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.

SHA-256: `0647b69c5cff36a0c68f73ab2031e45dcae47a347da99bc4661c6edc4fd54dc6`. Selected lines: `[[40, 117]]`.

The projection is literally Sigma.desc of the identity maps from the I-indexed coproduct. I is finite in the original universe; the base is any actual scheme. Its finiteness, etaleness, arbitrary-base-change square and native Hom.finrank = Nat.card I are proved for that same morphism.

| Original declaration | Native declaration | Source line |
| --- | --- | --- |
| `AlgebraicGeometry.SplitProjection.projection` | `AlgebraicGeometry.Scheme.SplitProjection.projection` | 40 |
| `AlgebraicGeometry.SplitProjection.etale` | `AlgebraicGeometry.Scheme.SplitProjection.instEtale` | 43 |
| `AlgebraicGeometry.SplitProjection.spec_comparison` | `AlgebraicGeometry.Scheme.SplitProjection.spec_comparison` | 47 |
| `AlgebraicGeometry.SplitProjection.finite_algebraMap` | `AlgebraicGeometry.Scheme.SplitProjection.instFiniteAlgebraMap` | 56 |
| `AlgebraicGeometry.SplitProjection.flat_algebraMap` | `AlgebraicGeometry.Scheme.SplitProjection.instFlatAlgebraMap` | 61 |
| `AlgebraicGeometry.SplitProjection.finite_spec` | `AlgebraicGeometry.Scheme.SplitProjection.instFiniteSpec` | 66 |
| `AlgebraicGeometry.SplitProjection.rank_spec` | `AlgebraicGeometry.Scheme.SplitProjection.rank_spec` | 70 |
| `AlgebraicGeometry.SplitProjection.baseChange` | `AlgebraicGeometry.Scheme.SplitProjection.baseChange` | 80 |
| `AlgebraicGeometry.SplitProjection.finite` | `AlgebraicGeometry.Scheme.SplitProjection.instFinite` | 89 |
| `AlgebraicGeometry.SplitProjection.rank` | `AlgebraicGeometry.Scheme.SplitProjection.rank` | 100 |
| `AlgebraicGeometry.SplitProjection.sigmaDesc_finite_etale_finrank` | `AlgebraicGeometry.Scheme.SplitProjection.sigmaDesc_finite_etale_finrank` | 107 |

Compilation evidence and actual provider identities are returned in the assigned scratch manifest. Compilation does not provide a theorem-family witness or mathematical-adoption status.
