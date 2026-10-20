# Relative Picard class and group compatibility

`Classes.lean` forgets the native `Scheme.RelativePicard` group-valued
functors to `Type (u + 1)`. Its base, family and normalized objects are the
actual native Picard groups and origin kernels. The class pullbacks and
natural transformations delegate to the native additive maps. The comparison
`familyMap_eq_familyScheme_map` identifies the incoming `pullback.lift`
formula with the native `pullback.map`, including both projections.

`Groups.lean` delegates the incoming group, quotient, splitting and forgetting
interfaces to `Picard/Presheaf.lean` and `Picard/Normalized.lean`. The historical
tensor theorem argument remains an explicit compatibility argument; the native
additive pullbacks are already proved. A section is used for normalization.
The quotient transition maps themselves need no section.

These definitions allow arbitrary original schemes and arbitrary test schemes,
including nonreduced and non-Noetherian tests. The native proper-flat Picard
sheaf comparison separately keeps its locally Noetherian original-base and
geometrically integral fibre assumptions. No representability statement is
introduced by this family.

Source: R5 packet revision `f8a3314ddecffcada2ec721d26d56a937bed9690`,
`R5Lab.Aglib.AlgebraicGeometry.Picard.Relative.{Basic,Group}`. The consuming
curve functors remain in `Aglib.AlgebraicGeometry.Curves.RelativePicard`.
