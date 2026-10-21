# Conjugation of actual inertia Kummer characters

`InertiaConjugation.lean` uses `GroupCohomology.Kummer` and preserves the source family's actual maps.

A decomposition-group element at the supplied absolute prime conjugates the actual inertia
subgroup to itself. The uniformizer Kummer character is equivariant for this conjugation, with
its original positive invertible level and DVR/fraction-field hypotheses. The generic cocycle
identity delegates to ContinuousH1.Cocycle.conjugation_value. The base ring and field retain
independent universes.

Source: `R5Lab.Aglib.GroupCohomology.Kummer.InertiaConjugation`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`b2a90f315e905795f836b6de8917e8ea57d893844882d5e24a7428ebc9af09d5`.

This correspondence records source identity and conditions. Compilation and final
package checks have their own scoped evidence; no downstream geometric realization
is asserted by this migration.
