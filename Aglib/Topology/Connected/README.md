# Connectedness through actual finite closed covers

`FiniteClosedCover` propagates a predicate through the actual pairwise
intersections of nonempty closed sets covering a connected space. Its component
image version retains a closed surjection from a Noetherian space, openness of
each actual irreducible component and connectedness of the target. It supplies
component arguments for downstream finite-cover geometry.

[LocallyConnected](LocallyConnected.lean) extends Mathlib's
`Mathlib.Topology.Connected.LocallyConnected` with Stacks 04MF: a space in which every point has a
Noetherian neighbourhood is locally connected
(`locallyConnectedSpace_of_forall_exists_noetherianSpace`), in particular every Noetherian space
(instance `TopologicalSpace.NoetherianSpace.locallyConnectedSpace`). In a Noetherian space every
connected component is open (`TopologicalSpace.NoetherianSpace.isOpen_connectedComponent`). No
separation axiom is assumed. Consumer: the scheme instance in
[Properties/Noetherian/LocallyConnected](../../AlgebraicGeometry/Properties/Noetherian/LocallyConnected.lean).
