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
The [regular-surface ideal theorem](../../IdealSheaf/Invertible/RegularSurface.md)
gives local rank one for the actual ideal module of an integral closed
subscheme with height-one actual stalk kernels, on a locally Noetherian
ambient scheme whose stalks are regular local of dimension at most two.

[Proper fibre descent](../../Morphisms/Proper/FibreDescent.md) factors a given
`g : X ⟶ Z` uniquely through a given proper surjective `f : X ⟶ Y` with
`IsIso f.c`, provided `g` is pointwise constant on its fibres. This theorem
works for arbitrary schemes, with no separation condition on `Z`; it creates
no contraction morphism. Point-blowup factorization, contraction and
minimal-model existence remain separate. General
[Milnor patching](../../../RingTheory/Etale/MilnorPatching/README.md), including
fibre-product flatness with surjective boundary map, flat component maps and
the original compatible tensor equivalences, is proved independently of these
surface endpoints.

The [finite-fibre neighborhood theorem](../../Morphisms/Proper/QuasiFinite.md)
gives an actual isomorphism neighborhood whenever such a proper birational
morphism has a finite point fibre, without a dimension or Noetherian bound.
The [regular-point blowup computation](../../Blowup/RegularPoint.md) separately
identifies its actual inverse-image centre with the original residue-field
projective line. Neither theorem supplies contraction or blowup factorization.

[TraitGraph](TraitGraph.md) constructs the actual common proper integral
Noetherian flat graph over a DVR from a supplied identification of the
literal generic fibres. Both projections are proper and surjective;
their generic comparisons and induced function-field equivalences retain
the original maps. Compatible supplied sections lift with both original
triangles. The lower [graph comparison](../../Morphisms/Proper/GraphClosure/Comparison.md)
uses the actual schematic image and schematic-density factorization.
Regularity and resolution of this graph remain separate obligations.
