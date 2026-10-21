# Geometric connectedness from the actual kernel action

`GeometricConnectedness.lean` compares the total scheme of a pulled-back cover
with the actual geometric base change of its original total scheme. The
canonical `totalBaseChangeIso` preserves both projections, its over-field
structure, and the actual field-valued point lift. These triangles identify the
existing geometric fibre functor with the original pointed fibre.

The actual geometric fundamental group maps to the original arithmetic
projection kernel via `GeometricKernel.geometricKernelHom`. The same fibre
identification intertwines evaluation of these actual groups.
`kernel_pretransitive_iff` uses the original `Stacks0BTX F` premise, properness
and geometric connectedness of the base scheme. The connected-cover criterion
uses the explicitly supplied Galois-category and fibre-functor classes on the
actual geometric base change. It retains nonemptiness of the fibre as well as
pretransitivity.

`Stacks0387 F` remains the original universal implication: connectedness after
the chosen algebraic-closure base change implies geometric connectedness of
every scheme over `F`. It retains `CharZero F`, quantifies over all displayed
schemes with no finite-type restriction, and has no global proof or instance.
The final `geometricallyConnected_iff_kernel_evaluation` combines exactly these
premises. It does not assume transitivity for a consumer-selected cover.

Source: `R5Lab.Aglib.AlgebraicGeometry.Morphisms.FiniteEtale.GeometricConnectedness`,
full packet source, SHA-256
`64ca2a144b6c241f3a0a117cc18a67a80114cb05f0a6b63452659569f87c567b`.
The full generic proof is retained under the native
`Scheme.FiniteEtale.GeometricCoverConnectedness` namespace. Source references
to Stacks tags `0387` and `0BTX` identify explicit premises; this migration
claims no new external verification of those statements. The current consumer
is actual multiplication-cover quotient surjectivity in
[MonodromyQuotient.lean](../../Group/MultiplicationKernel/MonodromyQuotient.lean).
