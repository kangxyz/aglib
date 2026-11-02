# Kernel transport and retraction splittings

[Ker](Ker.lean), imported as `Aglib.Algebra.Group.Subgroup.Ker`, adds
`MonoidHom.range_eq_ker_of_equiv`. Three multiplicative equivalences and the two stated
commuting equations transport a range-equals-kernel equality between two composable pairs
of group homomorphisms. The groups have the source theorem's common universe; no
commutativity or additional exactness structure is assumed.

[KerEquiv](KerEquiv.lean), imported as `Aglib.Algebra.Group.Subgroup.KerEquiv`, adds
`AddMonoidHom.retractionAddEquiv : A ≃+ B × ker r` for a retraction `r : A →+ B` with a
section, `c ↦ (r c, c - s (r c))`, and `AddMonoidHom.kerAddEquivOfComm`: an additive
equivalence of sources and an injective additive map of targets, commuting with two additive
maps, give equivalent kernels. The groups are commutative, in arbitrary universes. The
consumer is the Picard tangent space.

[KerSurjective](KerSurjective.lean) proves that a surjection `r : A →+ B`
restricts to a surjection on `ker d` when `d` maps `ker r` onto its codomain.
The statement chooses no lift; curve Picard restriction uses this correction.
