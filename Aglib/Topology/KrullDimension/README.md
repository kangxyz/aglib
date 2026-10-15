# Dimension of closed topological subspaces

[ClosedSubspace](ClosedSubspace.lean), imported as `Aglib.Topology.KrullDimension.ClosedSubspace`, owns `TopologicalSpace.topologicalKrullDim_closed_le_of_avoids_genericPoints`. In a quasi-sober space, a closed subset avoiding all component generic points has dimension at most `d` when the ambient dimension is at most `d+1`. The dimension comparison does not require Noetherianity.

`genericPoint_exists_open_disjoint` separately requires a Noetherian space: an open missing a component generic point has a disjoint open neighborhood of that point. The hypotheses of this auxiliary neighborhood result must not be transferred to the dimension statement merely because they share a file.

The actual objects are closed subsets, irreducible closed chains and generic points, with no sheaf, scheme or cohomology input. [Scheme Noetherian cohomological dimension](../../AlgebraicGeometry/Cohomology/Vanishing/README.md) consumes this lower topological dimension reduction.
