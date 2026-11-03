# The original ideal on a normalized-point chain

Source: [Ideal.lean](Ideal.lean).

Let `A` be a commutative integrally closed Nagata domain of dimension at most
two, and let `J : Ideal A` be nonzero.
`exists_ideal_image_isLocallyRankOne_of_nagata_base` constructs a finite
normalized-point chain `beta : T ⟶ Spec A` and a comparison `a` to the
ordinary ideal blowup `NormalizedBlowupCover.Base.source A J hJ`.

The original structural triangle is retained. The terminal is integral,
normal, Noetherian and of dimension at most two; both maps are proper,
dominant and birational through their original function-field maps.
The theorem identifies the ordinary blowup ideal pulled along `a` with
`(affineCenter A J).comap beta` and proves that this actual image ideal's
module is locally rank one.

The construction combines `AffineBase` with the ordinary blowup's Cartier
ideal and its dominant, possibly nonflat, ideal comparison.
The terminal need not be regular or Gorenstein. Applying the result to a
canonical numerator still requires the original Nagata and dimension
hypotheses; a stalk embedding alone does not provide them.
