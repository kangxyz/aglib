# Finite-type restriction comparisons

[Comparison](Comparison.lean), imported as
`Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Restriction.Comparison`, uses the
native `Scheme.Modules.QuasiCoherent` namespace.

`affineLocallyFiniteType_restrict_opensRange` passes finite type from restriction along an
open immersion to restriction to its actual open range. `affineLocallyFiniteType_of_restrict_top`
detects finite type on the top open. These statements hold on arbitrary schemes.

`finiteTypePrincipalRestrictionSquare` compares the actual global restriction on spectra
with the affine principal restriction under the finite-type affine equivalences. Its
component maps are the original canonical comparison, with no Noetherian premise introduced.
The [coherent localization specialization](../../../Coherent/Localization/README.md) retains
the Noetherian hypotheses needed for the Serre-localization conclusion.
