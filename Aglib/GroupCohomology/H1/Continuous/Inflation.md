# Continuous cocycle descent through quotient homomorphisms

`Inflation.lean` uses `GroupCohomology.ContinuousH1.Inflation` and preserves the source family's actual maps.

A continuous cocycle descends along a continuous group homomorphism that is a quotient map when
the coefficient actions agree and the cocycle vanishes on its kernel. The compact-to-Hausdorff
version derives the quotient-map hypothesis from surjectivity. No descent through a bare
surjection is asserted.

Source: `R5Lab.Aglib.GroupCohomology.H1.Inflation`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`521fcfca30111a38af356687ede479e369593bd6c91315ff6a408f83de63db89`.

This correspondence records source identity and conditions. Compilation and final
package checks have their own scoped evidence; no downstream geometric realization
is asserted by this migration.
