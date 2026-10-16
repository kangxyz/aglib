# Canonical Cech tensor maps for supplied fibre squares

[Cartesian](Cartesian.lean), imported as
`Aglib.AlgebraicGeometry.Cohomology.Cech.ModuleBaseChange.Cartesian`, proves
invertibility of the original `moduleCechTensorMapAlong` for a supplied
cartesian square over `Spec B → Spec A`, using the actual module pullback
unit. Its structural ring actions come from the supplied maps to the spectra
and the native `ΓSpecIso`.

The family is finite and affine in a separated source scheme, and the
coefficient module is arbitrary quasicoherent. No covering hypothesis,
flatness, Noetherianity or cohomological-finiteness premise is needed for
this complex isomorphism. The preceding tuple-intersection theorem does not
require the indexing family to be finite. These statements extend the
[original chosen-fibre-product construction](../ModuleBaseChange.lean)
without changing its maps or public APIs.
