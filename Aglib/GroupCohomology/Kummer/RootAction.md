# Galois action on roots of base-field units

`RootAction.lean` uses `GroupCohomology.Kummer` and preserves the source family's actual maps.

For every field and every natural level, the actual unit action fixes the image of a base-field
root of unity. The nth power of any root of a base-field unit is fixed as well. These
statements use the existing roots, coefficient inclusion and unit action, including level zero.

Source: `R5Lab.Aglib.GroupCohomology.Kummer.RootAction`, R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`, SHA-256
`3cbce6edfa4dbba1bf005acf3537fd9d6b6ee425a0996f8e951a4772c9c68b32`.

This correspondence records source identity and conditions. Compilation and final
package checks have their own scoped evidence; no downstream geometric realization
is asserted by this migration.
