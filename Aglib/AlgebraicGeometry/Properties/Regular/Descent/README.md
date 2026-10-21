# Descent of actual regular stalks

[FlatLocal](FlatLocal.md) supplies
`Scheme.RegularityDescent.flatLocalRegularityDescent`, an inhabitant of the
original `FlatLocalRegularityDescent` family. It proves regularity of the source
of an actual flat local homomorphism between Noetherian local rings when the
target is regular, with flatness induced by that same homomorphism. The lower
[ring theorem](../../../../RingTheory/RegularLocalRing/FlatDescent.md) allows
independent ring universes and requires no finite-type, unramifiedness,
characteristic or completion premise.

The existing `regular_at_image` and `regular_of_etale_cover` interfaces in
[FlatLocal.lean](FlatLocal.lean) retain their parametric input and accept this
supplied proof. They concern the actual stalk maps and the existing
`Scheme.RegularStalks` predicate, with their original flatness, locality and
local Noetherian hypotheses. Regularity ascent along étale maps remains with
the existing étale stalk provider.
