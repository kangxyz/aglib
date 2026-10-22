# Actual module maps over scheme limits

This pair owns Hom and equality descent for two finitely presented module
sheaves already given at one stage of a cofiltered diagram of qcqs schemes
with affine transition maps. It imports the affine spectral suppliers from
[Affine.lean](Affine.lean); global object descent is a separate consumer.
No Noetherian, coherence, flat-transition or injective-transition hypothesis
is used.

`pullbackConeCompIso D c q` is the native comparison
`pullback (c.π.app i) ≅ pullback (D.map q) ⋙ pullback (c.π.app j)`
for the actual arrow `q : j ⟶ i` and the original cone equation.

`exists_hom_equality_above_of_isLimit` descends equality of two actual stage
maps to one later stage. Quasi-compactness suffices for this equality theorem:
a finite affine cover, the actual affine equality producer, and a common
cofiltered stage give equality on a covering family of actual pullbacks.
The original sheaf-Hom uniqueness theorem then gives the global equality.
The affine transport uses `isoSpec` and the original global-section maps.

`pullbackTriangleIso` and `pullbackHomOfTriangle` retain actual commuting
triangles. Their composition identity is the original native pullback
associativity theorem. The existing canonical square comparison `pullbackSquareIso` from
`Modules.BaseChange.Affine.Mate` and its
cone-composition identity supply the exact coordinate transport for the
actual affine-scheme Hom producer. Pullback along `isoSpec` is fully faithful,
so its native preimage retains an actual map recovery equation.
The ring diagram, its colimit cocone and every scheme comparison are
constructed from the original `Γ` diagram and `isoSpec` naturality. Their
existential unpacking keeps concrete coordinate definitions out of the sheaf
calculation; the public theorem takes no coordinate-family premise.

`exists_hom_above_of_isLimit` is the global Hom producer. It uses
actual affine-scheme and relative-affine producers, finite common-stage chart
lifts, actual overlap equality synchronization, and native Hom gluing. Its
recovery equation is the specified original `pullbackConeCompIso` square.
`exists_relative_hom_above_of_isLimit` retains fixed original coefficient
sheaves on a base scheme and the actual structural maps of the diagram.
Quasi-separatedness enters through compactness of the original pairwise
affine overlaps. The public statements retain the actual prescribed stage
sheaves and the actual limit arrow throughout the construction.

The whole canonical module passed native compilation as Lean source
`a946457d35f2db7a11f02bbbf85f88d08e27c0983bf0336af8d4c828a0758e23`
in `remote-7b6eb8b9bc144b85a598412ec06568fa`, SOURCE
`d68f033b087ecaa8ac2ae710abf32d13050983da2bb2d109b0ea8280675a75f0`.
This covers global Hom, global equality, the fixed-base corollary and their
supporting comparisons at the stated generality. The later Properties
consumer failed separately; no consumer completion is claimed here.
Compiler coverage does not replace independent mathematical review.

Input basis: original Aglib HEAD
`3a4d549981ced306d89d3ed55418c9e6a25f86c4`. The earlier spreading assignment
remains separately frozen and is not a source of evidence for this pair.
