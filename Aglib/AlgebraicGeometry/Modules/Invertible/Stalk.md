# Local rank one from actual stalk frames

For a finitely presented module sheaf `M` on any scheme,
`isLocallyRankOne_iff_stalkLinearEquiv` identifies actual local rank one
with existence of a linear frame of every original module stalk over its
original local ring.

The pointwise-to-local direction uses `fittingIdealSheaf_stalkIdeal`,
stalkwise equality of actual ideal sheaves, and the existing Fitting
criterion for `SheafHasRank M 1`. The native rank-one equivalence supplies
the same `Invertible.IsLocallyRankOne` proposition used by line bundles.
It does not replace local bases by a newly defined pointwise predicate.

`nonempty_stalkLinearEquiv_of_isLocallyRankOne` proves the converse without
a separate finite-presentation hypothesis. Pullback to the original local
spectrum is a line bundle, hence is trivial there; the original
`stalkFromSpecStalkSectionsIso` recovers the original stalk frame.

No Noetherian, reducedness, field or characteristic hypothesis is used.
The result does not give a global frame or compatible choices of the
individual stalk frames. Its immediate consumer is the actual canonical
sheaf of a normal surface with intrinsically Gorenstein local rings.
