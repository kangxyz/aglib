# Continuous first cohomology

`Continuous` owns `GroupCohomology.ContinuousH1`, the single additive quotient
of bundled continuous crossed homomorphisms by principal cocycles. It retains
the actual coefficient topology and continuous additive action; discreteness or
continuity of group multiplication is required only where stated.

`SplitExtension` owns `GroupCohomology.PointedCohomology`: the split-coordinate
cocycle model, identified with that common quotient, and the kernel of section
restriction. `SplitCoefficients`, `SplitCoordinates` and
`SplitCoordinateNaturality` retain the actual coefficient and split-coordinate
maps. The pointed kernel/character equivalence keeps its specified forward
representative and continuity hypotheses.

`AffineTorsor` constructs the tagged affine carrier in
`ContinuousH1.AffineTorsors`, used by actual finite torsor comparison.
`PrimitiveCharacters` keeps exact-order, equivariance and translation
transitivity statements under their original finite cyclic coefficient and
action hypotheses. Generic split topological groups and equivariant quotient
algebra are lower dependencies. Current consumers are finite-etale monodromy
and actual small-etale finite-coefficient H1; no new identification with an
unprovided cochain-complex or geometric realization is asserted.

[Continuous/GroupEquivalence](Continuous/GroupEquivalence.lean) uses the supplied
mutually inverse group and coefficient pullback maps on the existing
continuous-H1 quotient. It retains the original cocycle values and independent
group/coefficient universes. Its character construction requires trivial action
only on the cohomology target; the native Kummer field comparison is a consumer.
