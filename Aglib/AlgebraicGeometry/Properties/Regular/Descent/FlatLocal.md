# Flat-local regularity descent

[FlatLocal.lean](FlatLocal.lean) supplies
`AlgebraicGeometry.Scheme.RegularityDescent.flatLocalRegularityDescent`,
an actual inhabitant of the original `FlatLocalRegularityDescent` family.

The family quantifies over commutative Noetherian local rings `A` and `B`, an
actual homomorphism `f : A →+* B`, locality of `f`, flatness of `f`, and
regularity of `B`. Its conclusion is `IsRegularLocalRing A`. Flatness is for
the module structure induced by that same `f`. The family has no finite-type,
unramifiedness, domain, characteristic or completion premise.

The proof consumes
`IsRegularLocalRing.of_flat_local` from
[FlatDescent.lean](../../../../RingTheory/RegularLocalRing/FlatDescent.lean).
That theorem has independent source and target universes and proves the full
scope of [Stacks Lemma 10.110.9, tag 00OF](https://stacks.math.columbia.edu/tag/00OF).

The existing `regular_at_image` and `regular_of_etale_cover` declarations keep
their original parametric interfaces. They accept the supplied
`flatLocalRegularityDescent` proof, with their original scheme hypotheses and
maps. This fills the generic mathematical premise used by their original R5
source; the extraction revision and source hash remain recorded in the Lean
module header.
