# Hilbert 90 through finite normal descent

`Hilbert90.lean` uses `GroupCohomology.ContinuousH1.Hilbert90` and preserves the source family's actual maps.

Finite Hilbert 90 is proved for the actual automorphism group of a finite-dimensional field
extension, without assuming the extension Galois. For a Galois extension, infinite descent uses
a finite normal intermediate field whose fixing subgroup kills the cocycle. The neighborhood
version constructs such a field from the identity fiber in the actual Krull topology.

Source: `R5Lab.Aglib.GroupCohomology.H1.ContinuousHilbert90`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`94ee62158132fce0325bf750e09c8dc57d90520574820cee72138006258a5e36`.

This correspondence records source identity and conditions. Compilation and final
package checks have their own scoped evidence; no downstream geometric realization
is asserted by this migration.
