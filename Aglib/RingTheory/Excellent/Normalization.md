# Finite normalization in dimension at most two

`Algebra.IsRegularMap.isReduced_of_isDomain` embeds the target of an actual
regular map from a domain into its generic fibre. The injection is the native
tensor-product inclusion, proved injective by flatness and the original
fraction-field map. Regularity of that fibre implies reducedness of the target.
This lemma has no dimension, locality, or Noetherianity assumption on the base.

`integralClosure.finite_of_regular_completion_of_dimLE_two` applies this to the
literal maximal-adic completion of a Noetherian local domain of Krull dimension
at most two, then uses the existing reduced-completion finiteness theorem. The
conclusion concerns the original integral closure in the supplied fraction ring.

`integralClosure.finite_of_isGRing_of_isJ0Ring_of_dimLE_two` patches these local
results for a domain with the genuine G-ring and J-0 properties. At each maximal
ideal it uses that exact component of `IsGRing`, not unproved stability of G-rings
under localization. The fraction-ring actions are the original localization
lifts. J-0 supplies a nonzero regular principal open; regular-local normality
makes it normal. The existing denominator-filtration patching theorem then
applies. Finiteness at all stalks alone is not a patching criterion.

`integralClosure.finite_of_isQuasiExcellentRing_of_dimLE_two` obtains J-0 from
the J-2 self-test and the regular generic point. Its hypothesis is the genuine
`IsQuasiExcellentRing.{u,0}` predicate, retaining the explicit test-algebra
universe. The conclusion is N-1, not the stronger Nagata/N-2 property.

These statements do not prove normal-domain completion of normalization
stalks, resolution existence, or the quasi-excellent resolution corollary.
The normal principal-open patching criterion is the one in
[Stacks 0333](https://stacks.math.columbia.edu/tag/0333).
