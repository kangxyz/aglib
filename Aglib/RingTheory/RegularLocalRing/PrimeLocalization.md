# Prime localizations of regular local rings

`IsRegularLocalRing.atPrime` proves regularity of `Localization.AtPrime p`
for every prime ideal `p` of a commutative regular local ring `R`.
`isRegularRing_of_regularLocal` packages all these conclusions in the
native `IsRegularRing R` interface. Neither result assumes global
regularity beforehand.

The finite `R`-module `R ⧸ p` has projective dimension bounded by the
dimension of `R`. Native module localization preserves that bound. The
localized-submodule quotient map identifies its localization with
`Rₚ ⧸ pRₚ`, and the native equality `pRₚ = maximalIdeal Rₚ` identifies
the latter with the actual residue field. The existing residue-field
projective-dimension criterion now proves regularity of `Rₚ`.

`of_isLocalizationAtPrime` transports this result to any actual
`IsLocalization.AtPrime S p` model using the canonical localization algebra
equivalence. The universes of `R` and this target model are independent.

The mathematical statement corresponds to the localization conclusion of
[Stacks Project, Lemma 10.110.6, tag 0AFS](https://stacks.math.columbia.edu/tag/0AFS).
The implementation uses the existing finite-module projective-dimension
bound and residue-field criterion, without requiring a separate global
dimension construction.
