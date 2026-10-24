# Actual affine direct-image resolution and localization

[Localization](Localization.lean) proves that
`moduleCohomologyRestrictionMap_isLocalizedModule_of_isPullback` is the
original localization map for the supplied localization square, every qcqs
morphism to a spectrum, every quasicoherent coefficient and every natural
degree. It uses the proved canonical qcqs tensor-map isomorphism and its
native scalar-adjunction mate. The coefficient arrow is the original
module pullback unit and the cohomology is unchanged `Sheaf.H`.

[Localization/Open](Localization/Open.lean) retains the original
restriction/pullback coefficient isomorphism and the original `E_top` and
`E_V` cohomology comparisons. The resulting localizing map is exactly the
unchanged `Sheaf.H'` restriction from the whole space to the indicated
actual open. Scalar compatibility uses native restriction of scalars
through the original endomorphism-ring action; no new action is imposed.

[Localization/Principal](Localization/Principal.lean) supplies the actual
square for each coordinate-ring element. Its source is the native
inverse-image open, and the other projection is the original restricted
morphism followed by the native affine-open `isoSpec`. The native
structure-sheaf localization algebra is retained. The lower
[affine-open geometry](../../../Morphisms/OpenImmersion/Affine.lean)
identifies the exact spectrum map in this square.

[Resolution](Resolution.lean) applies these results to a supplied actual
module injective resolution `I`, pushed forward termwise. The native
section-complex restriction is localizing in every nonnegative degree
through the original open-resolution cohomology equivalence and its actual
restriction naturality. The original zero extension of `I` supplies the
negative degrees. Thus
`moduleResolutionPushforwardTildeCounit_quasiIso f M I` proves the literal
native affine tilde–global-sections counit on
`((Modules.pushforward f).mapHomologicalComplex (.up ℤ)).obj I.cochainComplex`
a quasi-isomorphism under precisely `QuasiCompact f`, `QuasiSeparated f`
and quasicoherence of `M`.

The counit components, section-unit formula and coefficient naturality
are the original native maps in [Modules.Complex.Tilde](../../../Modules/Complex/Tilde.lean).
There is no flatness, Noetherianity, finite-generation or additional
theorem-family premise. This genuine chain comparison supplies the affine
model for actual higher direct images and native derived direct-image
models; a cohomology-only identification is not substituted for it.

[Cohomology](Cohomology.lean) gives
`moduleHigherDirectImageAffineSectionsLinearEquiv`: sections of the actual
native higher direct image are unchanged original `Sheaf.H`, with the specified
structural action. Its forward formula retains Gamma of the original affine
higher-image comparison, inverse original tilde unit, homology of the actual
pushforward/global-sections complex comparison, and the original resolution
class. `moduleDerivedPushforwardSingleAffineSectionsLinearEquiv` uses the
shared native Rn/derived-single homology comparison for the installed bounded
below right-derived functor. These are linear equivalences across the native
section and original Ext-cohomology universes; no smaller replacement H is
introduced. The derived-single homology sheaves are quasicoherent under exactly
qcqs of the original morphism and quasicoherence of the coefficient.

[Cohomology/Naturality](Cohomology/Naturality.lean) proves coefficient
naturality of the original affine higher-image iso for every supplied native
resolution lift. The section/cohomology linear equivalence takes the actual
`rightDerived n` coefficient arrow to the unchanged `moduleCohomologyMapOfHom`
for arbitrary supplied resolutions; native resolution descent discharges the
lift internally. The corresponding equation for homology of the installed
`RF` at the original single follows from the shared native single-homology
iso. The original counit, tilde unit, structural scalar action and large
cohomology universe are retained throughout.

[Cohomology/Restriction](Cohomology/Restriction.lean) proves
`moduleHigherDirectImageAffineSectionsLinearEquiv_openRestriction` for an
actual cartesian open square between affine targets. Under the original
affine section equivalences, the native higher-image open comparison on
the original restriction-unit section is exactly
`moduleCohomologyMapAlong` for the original source restriction unit. The
source morphism is qcqs and the original coefficient is quasicoherent;
target qcqs follows from the square. Supplied original resolutions and
all natural degrees, including zero, are retained. The generic resolution
formula is imported from its sole
[lower owner](../Restriction/Resolution.lean).

[Single](Single.lean) gives the actual installed
`Scheme.Modules.affineDerivedPushforwardSingleIso f M`: for any affine
morphism and any quasicoherent coefficient, `RF(single₀ M)` is the native
single of the original ordinary `f_* M`. The isomorphism is the shared
coefficient-specific acyclic-single comparison. Its unit equation retains
the installed `derivedPushforwardPlusUnit` and original single-complex map;
its naturality equation retains each original coefficient arrow. The
native derived single has cohomological bounds `[0,0]`. No finite or
Noetherian hypothesis is needed, and exactness of affine pushforward on
all module sheaves is not asserted. The exact source passed with receipt
`1792118800962100000-93177` in 3.1 seconds at the default budget. The
independent arbitrary-universe `AffineDerivedSingleConsumer.lean` passed
with receipt `1792118853978467000-93984`; all five inspected declarations
use only the three standard axioms. Finite coherent direct images consume
this actual unit-normalized comparison.

[DerivedModel](DerivedModel.lean) transports an actual bounded-below module
complex's isomorphism to installed derived global sections into an actual
isomorphism from its native tilde to installed derived direct image over
`Spec R`. It uses the same original injective resolution and the literal
identity-on-sections comparison of its pushforward. The forward formula
retains exact tilde's original derived units, the actual module-model
isomorphism, the original tilde/sections counit and the original
resolution-derived comparison. The intermediate helper accepts the
quasi-isomorphism of that concrete counit; the public qcqs/quasicoherent
constructor discharges it with the proved theorem above. No global-section
exactness, injectivity of pushed resolution terms, termwise quasicoherence,
Noetherianity or finite-projective hypothesis is imposed.

This object transport selects no additional chain representative. Its
equality to a separately chosen chain-normalized model comparison is a
further normalization obligation, and is not asserted here. The exact
source passed `1792125295233946000-79252` in 16 seconds at the default
budget. The independent arbitrary-universe
`AffineBaseDerivedModelConsumer.lean` passed
`1792125337528449000-79639`, checking both the concrete-counit helper and
the unconditional qcqs/quasicoherent constructor, the literal counit
components and identity-on-sections formula. All six inspected
declarations use only the three standard axioms.

[GlobalSections](GlobalSections.md) compares installed derived global sections
after the original affine pushforward, for every quasicoherent coefficient.
The target need not be affine; its specified structural scalar map is
composed with the actual map on global sections. The resulting original
cohomology linear equivalence preserves units and coefficient naturality,
without Noetherianity or properness. Its current consumer is the finite
trace-coordinate cohomology comparison.
