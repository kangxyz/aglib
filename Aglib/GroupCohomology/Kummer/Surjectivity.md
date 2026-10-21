# Characteristic-zero Kummer surjectivity

`Surjectivity.lean` uses `GroupCohomology.Kummer` and preserves the source family's actual maps.

For a field of characteristic zero, every actual continuous roots-of-unity cocycle has a
unit/root representative at every natural level. The actual Kummer class map is surjective at
positive levels. These results specialize the perfect-field route through exactly the same
base-unit map, cocycle and Kummer class.

Source: `R5Lab.Aglib.GroupCohomology.Kummer.Surjectivity`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`1717b468026d3ebf27c81973c57ae78e884285e14485d686080994996a7f7959`.

This correspondence records source identity and conditions. Compilation and final
package checks have their own scoped evidence; no downstream geometric realization
is asserted by this migration.
