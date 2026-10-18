# Actual Kahler differentials and canonical pullback

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.Modules.Differentials.Basic`, owns `Scheme.Modules.Differentials`. For an actual field scheme, `differentialPresheaf` is the relative Kahler differential presheaf and `differentialSheaf` its actual module sheafification. `differentialSheafHomEquiv` is the universal derivation interface against an actual module sheaf.

`differentialSheafDerivation`, `differentialPushforwardMap` and `differentialPullbackMap` use the actual structural map and adjunction. The map sends `d(a)` to `d(f# a)` and has genuine hom-extensionality and identity/composition formulas. Smoothness or etaleness is not needed to construct these maps; fields and schemes retain universe `u`.

[EtalePullback](EtalePullback.lean) proves `Scheme.Modules.Differentials.EtalePullback.isIso_differentialPullbackMap` for the actual canonical arrow of an etale field-scheme morphism. `Scheme.Modules.Differentials.etaleDifferentialIso` is `asIso` of that same arrow, and `etaleDifferentialIso_hom` is its exact `rfl` hom equation. No global supplier premise is required.

[SmoothRank](SmoothRank.lean) proves `Scheme.Modules.Differentials.differentialSheaf_hasRank_of_smooth K X n hX` over every field in the source universe and in every smooth relative dimension. Actual standard-smooth affine charts supply the local bases. `Scheme.Modules.Differentials.smoothDifferential_finiteLocallyFree X n hX` consumes that proved rank. The former global theorem-family premises and the empty `Properties` entry are retired. The actual successors are `SmoothRank` and `EtalePullback`.

Lower actual module pullback, structural maps and [rank/class](../LocallyFree/README.md) interfaces feed the maps. General differential consumers use them without a canonical-bundle degree, genus or curve Riemann–Roch assertion.

The minimal direct selection from local Aglib main `40af743` is recorded in
[the migration manifest](../../../../docs/migration/upstream-smooth-differentials.json).
Each selected leaf and the independent public consumer passed at the default
budgets. The standard-smooth basis supports independent ring and algebra
universes. The global rank theorem retains the source universe and includes
the empty scheme. [ExteriorPower](../ExteriorPower/README.md) constructs the
actual top exterior line from a specified rank witness.
[Projective differentials](../../ProjectiveSpace/Differentials/README.md)
prove the global Euler sequence and determinant/twist formula. The
[canonical comparison](../../Cohomology/Duality/Projective/Canonical.lean)
identifies the actual closed right-adjoint value with the top differential
single for a closed immersion between schemes smooth of fixed dimensions
over the same arbitrary base.

[Affine](Affine.lean) is the sole arbitrary-ring owner of
`affineRelativeConstants`, the native constant-base differential presheaf,
its original localization seed and `affineRelativeDifferentialIso`.
The implementation was extracted from the second generic block of
`SmoothRank`; its former qualified names remain public compatibility exports.
The still more general affine presheaf sheafification/tilde comparison now
lives in [Localization/AffineSheafification](../QuasiCoherent/Localization/AffineSheafification.lean).
Neither lower owner imports field geometry or cohomology, and the original
seed, differential and sheafification equations are unchanged.
`affineRelativeDifferentialIso_hom_d` identifies the image of the original
sheafified differential on every principal open with `tilde.toOpen` of the
original ring differential. This normalization is owned here independently
of the scheme-relative comparison that consumes it.

[Relative](Relative/README.md) constructs the actual relative differential
sheaf for arbitrary scheme morphisms using the original structure map.
Its universal property holds for every coefficient module sheaf. The
affine-base derivation equivalence and actual differential-sheaf comparison
use native principal localization and sheaf separatedness, without a
quasicoherence premise on the coefficient. `Relative.Affine` combines this
bridge with the lower affine owner to identify the actual general relative
sheaf on `Spec.map σ` with the tilde of the original Kähler module. Both
principal-open differential formulas and actual quasicoherence are proved.

`Relative.Restriction` retains the actual derivation under source and base
open restrictions. `Relative.SmoothRank` proves finite local freeness and
the displayed rank for every smooth morphism of fixed relative dimension
over arbitrary bases, using its native standard-smooth local frames.
No field, Noetherianity, coefficient family or quasi-compactness premise
is added. The [relative Serre family](../../Cohomology/Duality/Projective/Relative/README.md)
now supplies the normalized trace over separated bases and coherent duality
over Noetherian separated bases, through the specified projective square
and chosen closed embedding. General proper duality and embedding
independence remain separate.
