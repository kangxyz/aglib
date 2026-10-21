# Regularity descent along actual etale maps

[Etale.lean](Etale.lean) applies
[the proved ring descent theorem](../../../../RingTheory/RegularLocalRing/EtaleDescent.lean)
to the actual scheme stalk map. Its declarations lie in
`AlgebraicGeometry.Scheme.RegularityDescent.Etale`, separately from the
conditional general flat-local interfaces in [FlatLocal.lean](FlatLocal.lean).

- `regular_at_image_of_flat_formallyUnramified f x hx` assumes
  `LocallyOfFiniteType f`, `Flat f`, `FormallyUnramified f`, a Noetherian
  target stalk at `f x`, and regularity `hx` of the source stalk at `x`.
- `regular_at_image f x hx` specializes this to `Etale f` with the same
  target-stalk Noetherianness and source regularity hypotheses.
- `regular_of_etale_cover C f covers regular` assumes a locally Noetherian
  target, an arbitrary jointly surjective family of actual etale maps, and
  regular stalks on every source. It concludes regular stalks on the target.

For the pointwise theorem, the source-stalk algebra is induced by
`(f.stalkMap x).hom.toAlgebra`. Locality, essential finite type, flatness and
formal unramifiedness are obtained for this same map from the scheme
morphism. Source Noetherianness follows from the supplied regularity of its
stalk. The cover theorem applies the pointwise theorem to a preimage of each
target point. It therefore needs no separate local Noetherianness assumption
on the source schemes.

The new interfaces take no `FlatLocalRegularityDescent` parameter. In an
etale-chart consumer, the descent call is
`Scheme.RegularityDescent.Etale.regular_at_image j x hx`; any independent
premises used to establish `hx` remain required. No assertion about general
flat-local descent is imported into this proof.

The [interface consumer](../../../../../AglibTest/EtaleRegularityDescent.lean)
checks independent ring universes, the actual `RingHom.toAlgebra` induced by
given ring-hom properties, the pointwise scheme interfaces, and the etale-cover
interface. Production suppliers and existing consumers are unchanged.
