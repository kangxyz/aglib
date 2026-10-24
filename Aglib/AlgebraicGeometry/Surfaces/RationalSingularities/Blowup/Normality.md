# Normality of the ordinary rational surface blowup

This module proves that the original normalization map of the ordinary
maximal-ideal blowup is an isomorphism. Its main results are
`normalization_isIso` and `ordinary_normalStalks`.

The base ring A is a commutative Noetherian Nagata local domain, integrally
closed and of Krull dimension two. The rationality input is the existing
`NormalModificationH1Vanishing A` predicate. The construction uses the
literal ordinary blowup and its generic normalization from
[Blowup](../Blowup.lean), and the original normalized power-section theorem
from [IdealPowers](IdealPowers.lean).

The original finite ideal generators define an affine quotient row. The
native framed-row construction, under the identity scalar base change,
gives `tautologicalEmbedding`. Its structural triangle is the original
blowdown, and `tautologicalEmbeddingTwistingIso` identifies the pullback of
positive O(1) with the actual exceptional ideal. Serre vanishing is applied
on this ordinary source with that positive twist.

The full power-centre subscheme maps define `idealPowerNormalizationUnit`
using the native ideal pushforward map. Its inclusion square is the
original normalization structural unit. Every scalar in m^n supplies an
ordinary ideal-power section. The normalized section-image theorem then
proves that this same power-normalization map is bijective on global
sections, with both original coefficient maps retained.

For positive powers, integral Cartier avoidance identifies the actual
ideal pullback. Its adjunction mate is the same power-normalization map.
`positivePowerProjection_unit` proves that the original projection formula
carries the tensor of the structural normalization unit to that map,
through the original right unitor. Consequently this tensor of the unit
is surjective on global sections.

The cokernel of the structural unit is coherent because normalization is
finite. A native negative-twist presentation gives an actual finite
generating row after an arbitrarily large positive exceptional-ideal
twist. The original H0 surjection and Serre H1 vanishing for the first term
together force the twisted cokernel's global sections to vanish. Its
actual row makes the twisted cokernel zero. The line-bundle tensor
equivalence cancels the twist, so the structural unit is an isomorphism.
The finite affine normalization map is then an isomorphism on each
original affine open. Normal stalks transfer along that same map.

No completeness, Gorensteinness, regular source, coefficient-field section
or chosen resolution is required. Finiteness of normalization, the matched
projective embedding, the section-image equality and the cokernel's
generating row are derived from their original maps and the stated
hypotheses. The module does not assume normality of the ordinary blowup.

The mathematical route is [Stacks 54.9.4, 0B4Z](https://stacks.math.columbia.edu/tag/0B4Z),
using the normalized section argument of
[Stacks 54.9.3, 0B4Y](https://stacks.math.columbia.edu/tag/0B4Y).
The exceptional-fibre quotient sections, their residue-field action and
Hilbert-function or Gorenstein consequences are separate consumers.
