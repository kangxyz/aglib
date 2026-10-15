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
