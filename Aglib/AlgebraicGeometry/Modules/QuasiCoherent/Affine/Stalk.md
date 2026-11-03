# Original affine sections and actual module stalks

For arbitrary `R : CommRingCat`, `Scheme.Modules.tildeIsoToModuleStalk`
composes native `tilde.toStalk` with an actual sheaf-isomorphism stalk map.
Its native localization theorem uses that same scalar-restricted map.
These two declarations and the following three affine declarations are
extracted once from the finite-source closed-adjoint stalk comparison;
its old public names remain thin wrappers.

For a module sheaf M on Spec R and an actual point x,
`affineSectionsToStalk` uses the native tilde map followed by the original
`fromTildeΓ` stalk map. `affineSectionsToStalk_apply` proves that its value
is literally the original top germ. `affineSectionsToStalk_scalar` records
that `StructureSheaf.toStalk` is the original `ΓSpecIso.inv` followed by
the top ring germ. The naturality law uses the original induced stalk map.
These value, scalar, and naturality laws require no quasicoherence.

Quasicoherence is needed only to make the counit an isomorphism, yielding
`affineSectionsToStalk_isLocalized` at `x.asIdeal.primeCompl`.
No domain, Noetherianity, normality, locality, dimension, finite-presentation,
or surface hypothesis is introduced. No replacement localized module is
chosen. Canonical generic framing and fraction-field embeddings are separate
consumers; the existing finite embedded-module numerator is unchanged.

Native recovery graph83 accepted lower source `422535e4` (3.6 seconds)
and the actual changed finite-source consumer `6257280e` (12 seconds).
The graph had an unrelated target failure; these are exact own-node passes,
not a whole-project result. The earlier unaccepted direct-germ draft is retired.
