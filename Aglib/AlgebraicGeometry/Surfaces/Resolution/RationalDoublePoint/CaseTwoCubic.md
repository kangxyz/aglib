# The actual ordinary chart and its nonzero residue cubic

API: [ordinary_saturatedChart_isIntegrallyClosed](CaseTwoCubic.lean#L43), [exists_original_cubic_of_normalized_kernel](CaseTwoCubic.lean#L66), [exists_original_cubic_of_singular_normalized_kernel](CaseTwoCubic.lean#L87).

This bounded geometric consumer takes a normal Noetherian Nagata local domain
of dimension two and its actual universal normal-modification H1 vanishing.
It uses the proved `ordinary_normalStalks` on the original ordinary blowup.
For a nonzero actual maximal-ideal element t, the existing native chart witness
and original spectrum-stalk isomorphism transport those actual normal stalks
to the prime localizations of the literal saturated t-chart. The existing
local criterion gives integral closedness of that original chart ring.
No chart or child ring is completed or declared finite over the original base.
At a singular actual two-dimensional local ring, the existing three-generator
Nakayama lemma proves that t is not in the maximal-ideal square, hence is
nonzero; the singular-point convenience theorem does not assume that extra
nonvanishing conclusion.

Given actual t,s,z generating the original maximal ideal and an actual full
canonical cotangent kernel equal to `(X₁²)` in the order s,z,t, the existing
`DoubleLinePresentation.ofKernel` supplies the original cone equivalence with
its original symbol and coefficient identities. The existing genuine cubic
producer then gives a true equation on t,s,z and a nonzero binary cubic over
the original residue field. It is packaged as the existing `CubicRelation`
with zero remainder, not a new relation object or a second DVR argument.

The full normalized kernel is an input. `CaseTwoCoordinates` constructs
these coordinates when a genuine full linear-square kernel is supplied.
The entry and continuation consumers use the resulting cubic; its other
coefficients remain unrestricted when a simple root is selected as marker.

Present consumers: [CaseTwoCoordinates](CaseTwoCoordinates.md), [CaseTwoTripleEntry](CaseTwoTripleEntry.md).
