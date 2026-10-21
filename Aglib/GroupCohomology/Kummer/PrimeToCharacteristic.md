# Kummer kernels and perfect-field surjectivity

`PrimeToCharacteristic.lean` uses `GroupCohomology.Kummer` and preserves the source family's actual maps.

For any field K and positive n nonzero in K, the actual continuous Kummer class vanishes
exactly on nth powers. Descent of a fixed closure element requires its separability.
Separately, over a perfect field every continuous roots-of-unity cocycle has an actual
unit/root representative for every n; surjectivity of the Kummer class map uses positive n. No
perfectness assumption is added to the kernel theorem.

Source: `R5Lab.Aglib.GroupCohomology.Kummer.PrimeToCharacteristic`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`a27d4071a4694154092163f92b404b77732af1e2e6dcde9c59d3f92040594ea6`.

This correspondence records source identity and conditions. Compilation and final
package checks have their own scoped evidence; no downstream geometric realization
is asserted by this migration.
