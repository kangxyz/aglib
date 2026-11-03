# The original projective field-extension quotient cover

Source: [ProjectiveCover.lean](ProjectiveCover.lean).

This construction retains the original closed immersion j into projective
space over k, the given extension k -> K and the same native scheme pullback.
The fields, coordinate index and schemes use the common universe required by
the original projective and scheme base-change APIs. The index need not be
finite. No Noetherianity, CM, coefficient, degree or homology premise is added.

`projectiveSourceQuotientChart` selects the original quotient chart over each
k-coordinate open once. Its arguments do not include K. The sole chart algebra
instance is the actual `coordinateRingMap (algebraMap k K)` converted with its
native `toAlgebra`; the quotient construction reuses this same action.

`projectiveBaseChangeQuotientChart` applies the accepted mapped-ideal chart
constructor and the original Cartesian projective coordinate square. It makes
no new quotient-ideal choice. Its ideal is literally the original source ideal
mapped by the original coordinate homomorphism. The source map beta retains
both actual Cartesian squares and both projection equations.

`projectiveBaseChangeQuotientCoverObjIso` is derived from that target-chart
square by native `IsPullback.isoPullback`. It is not an input. The open cover
uses `Scheme.Cover.copy` on the original target-coordinate cover pulled back
along the second projection of the same scheme pullback. Its index, objects
and arrows are literally the original index, mapped-ideal spectra and beta
maps. The copying equation is the native `isoPullback_hom_fst` law. No new
point-surjectivity proof or general cover backend is implemented.

The exact imports are QuotientChart, ProjectiveSpace.BaseChange.ChartPullback
and native Cover.Open. No Localization, Composition or SourcePresentation
import is added. FiniteSource.Derived remains a transitive dependency through
the accepted chart type; this is not a homology-free import closure.
