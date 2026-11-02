# Finite original residue maps at closed points

Import `Aglib.AlgebraicGeometry.Morphisms.FiniteType.ResidueField`.

`Scheme.Hom.residueFieldMap_finite_of_closedPoint` proves finiteness of the
ORIGINAL residue-field homomorphism at a globally closed source point of an
arbitrary locally finite-type morphism. No properness, Noetherianity, base
closedness or surface dimension hypothesis is required.

The source residue-spectrum map is a closed immersion. Its original
factorization through the image residue field makes the residue-spectrum
map locally finite type, hence its original ring map finite type. The native
field/Jacobson theorem then gives finiteness. No substitute field embedding
or residue-field identification is chosen.

This is the one proof formerly owned by
`Surfaces.Birational.NormalizedPointDomination.ResidueTranscendence`; that
old public theorem remains a same-statement thin caller.
