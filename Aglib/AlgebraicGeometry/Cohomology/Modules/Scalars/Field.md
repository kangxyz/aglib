# Original field-constants cohomology

Source: [Field.lean](Field.lean).

For a field `k`, a field-scheme `X`, any module sheaf `M`, and every natural degree,
`moduleCohomologyConstantsIso` identifies the existing module-valued cohomology for
`constants X` with the existing `moduleCohomology k X M q`.

The construction transports only the `Module` structure field along the original
`moduleCohomologyModuleOfHom_constants` equality. Its underlying map is the identity
on the same original sheaf-cohomology group, as recorded by the value theorem.
No finiteness, coherence, dimension, or projectivity hypothesis is required.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/CohenMacaulayCurve/Serre/Field](../../Duality/Projective/Relative/CohenMacaulayCurve/Serre/Field.md).
