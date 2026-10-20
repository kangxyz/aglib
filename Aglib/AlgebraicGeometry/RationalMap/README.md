# Actual graph closures over a field

[Graph](Graph.lean), in `Scheme`, constructs the literal graph map from an open
of a field scheme into a fibre product and then takes its actual schematic
image. It retains both projections and their triangles. Properness of each
projection has its own properness hypothesis on the opposite field scheme.
Image integrality, dominance, Noetherianity and the isomorphism over the
original open retain their separate displayed assumptions.

This is a graph-closure construction over a field. It does not construct a
common regular domination or a graph closure over an arithmetic trait. The
native curve projectivity constructions use this exact field graph.

The proof reuses the actual schematic-image integrality and the open-section
restriction theorem from their lower native owners.
