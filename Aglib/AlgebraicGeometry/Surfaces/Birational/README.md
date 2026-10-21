# Birational surface isomorphism locus

[IsomorphismLocus](IsomorphismLocus.md) describes the actual
`Hom.targetIsomorphismLocus`, the union of all target opens on which the literal
restriction of the original morphism is an isomorphism. The restriction to
this union is an isomorphism, and every such open is contained in it.

For integral source and target, Noetherian target with `NormalStalks`,
`topologicalKrullDim Y ≤ 2`, proper dominant `f` and invertibility of the
actual `functionFieldMap f`,
`exists_isIso_restrict_finite_closed_complement_of_isProper_birational`
gives this maximal open with a finite complement consisting of closed points.
The source need not be regular; no excellence or projectivity is assumed.
The proof uses the valuation-ring extension theorem at points of coheight at
most one and Noetherian scheme sobriety for finiteness of the complement.

The lower [birational functions theorem](../../Morphisms/Proper/BirationalFunctions.md)
has no Noetherian premise; the
[geometric-connectedness specialization](../../Morphisms/Proper/ConnectedFibres.md)
retains local Noetherianity. The separate
[height-one principal theorem](../../../RingTheory/RegularLocalRing/HeightOnePrincipal.md)
concerns actual ideals in regular local rings of dimension at most two.
These endpoints supply no point-blowup factorization, contraction, minimal-model
existence or Milnor fibre-product flatness theorem.
