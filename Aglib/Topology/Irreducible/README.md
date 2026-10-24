# Irreducible components

`ClosedCover` identifies an irredundant closed irreducible cover in a quasi-sober
space with the actual irreducible-component family. The generic-point argument
requires no finite-index hypothesis. The separate two-member theorem works for
arbitrary topological spaces and retains noncontainment in both directions;
it also computes the actual component cardinality. These are component
inventory inputs for downstream affine-cover arguments.

[LocallyFinite](LocallyFinite.lean): for a space in which every point has a Noetherian neighbourhood
(Stacks 0051), the irreducible components form a locally finite family
(`locallyFinite_irreducibleComponents_of_forall_exists_noetherianSpace`, through Mathlib's
`preimage_mem_irreducibleComponents` on a Noetherian open neighbourhood), so every union of
components is closed
(`isClosed_sUnion_of_subset_irreducibleComponents_of_forall_exists_noetherianSpace`). In a
quasi-sober space the generic point of a component lies in no other component
(`genericPoint_notMem_sUnion_irreducibleComponents_diff`). Homogeneity criterion
(`irreducibleSpace_of_forall_exists_noetherianSpace_of_forall_exists_homeomorph_closedPoints`): a
connected, quasi-sober, Jacobson such space whose homeomorphisms act transitively on its closed
points is irreducible. No separation axiom beyond quasi-sobriety is used. Consumer:
[Group/IdentityComponent/Irreducible](../../AlgebraicGeometry/Group/IdentityComponent/Irreducible.lean).
