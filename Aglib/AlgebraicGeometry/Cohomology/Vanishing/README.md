# Noetherian Zariski cohomological dimension

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.Cohomology.Vanishing.Basic`, defines `AlgebraicGeometry.Scheme.Cohomology.NoetherianSheafCohomologyVanishing` directly on actual `Sheaf.H`. It quantifies over Noetherian schemes, arbitrary abelian sheaves and natural `d,n`, with `topologicalKrullDim X ≤ d` and `d < n`.

[Noetherian](Noetherian.lean) supplies `noetherianSheafCohomologyVanishing` and its pointwise vanishing theorem: cohomology above that dimension bound is subsingleton. No properness, quasicoherence, coherence, reducedness or field hypothesis is required. The cohomology/Ext universe remains the source's `u+1`.

The route uses actual [topological filtered-colimit/support/Godement](../../../Topology/Sheaves/README.md) interfaces and [closed-subspace dimension reduction](../../../Topology/KrullDimension/README.md). These generic prerequisites are separate source owners. The endpoint imports the vanishing definition directly, without a proper-coherent-finiteness input.
