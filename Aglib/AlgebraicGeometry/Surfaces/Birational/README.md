# Birational surface maps, common domination and factorization

## Isomorphism locus

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
no contraction morphism. The point-blowup factorization below uses this
descent theorem; contraction and minimal-model existence remain separate. General
[Milnor patching](../../../RingTheory/Etale/MilnorPatching/README.md), including
fibre-product flatness with surjective boundary map, flat component maps and
the original compatible tensor equivalences, is proved independently of these
surface endpoints.

The [finite-fibre neighborhood theorem](../../Morphisms/Proper/QuasiFinite.md)
gives an actual isomorphism neighborhood whenever such a proper birational
morphism has a finite point fibre, without a dimension or Noetherian bound.
The [regular-point blowup computation](../../Blowup/RegularPoint.md) separately
identifies its actual inverse-image centre with the original residue-field
projective line. These are inputs to factorization below; contraction requires
further results.

## Common domination and trait models

[CommonDomination](CommonDomination.md), in `Scheme.CommonDomination`,
starts with an integral Noetherian `X` with regular stalks and dimension at
most two, an actual map `pX : X ⟶ Spec R` over a Noetherian commutative
ring, and an integral target proper over the same base. The original
dominant `gη : Spec K(X) ⟶ T` and its base triangle are inputs.
`exists_pointBlowupChain_extension_to_proper_target` produces a finite
point-blowup chain `β : Y ⟶ X` and a dominant extension `h : Y ⟶ T`,
with regular integral Noetherian `Y` of dimension at most two. It retains
the base triangle, the generic triangle through the canonical
`functionFieldMap β`, and an actual `j : Spec K(X) ⟶ Y` with
`j ≫ β = ηX` and `j ≫ h = gη`. The construction uses the actual Chow
modification, [projective extension](../../RationalMap/ProjectiveExtension.md)
for its finite product factors, and the finite-map integral generic lift.
When `pX` is proper,
`exists_proper_pointBlowupChain_commonDomination` also makes `h` proper
and surjective. Birationality of `h` requires a corresponding original
generic isomorphism.

[TraitGraph](TraitGraph.md) constructs the actual common proper integral
Noetherian flat graph over a DVR from a supplied identification of the
literal generic fibres. Both projections are proper and surjective;
their generic comparisons and induced function-field equivalences retain
the original maps. Compatible supplied sections lift with both original
triangles. The lower [graph comparison](../../Morphisms/Proper/GraphClosure/Comparison.md)
uses the actual schematic image and schematic-density factorization.
Regularity of the graph itself is not asserted by this construction;
regular-source domination is supplied below.

[TraitDomination](TraitDomination.md), in `Scheme.TraitDomination`, starts
with the original DVR `R`, specified fraction field `F`, proper flat
integral `p : X ⟶ Spec R`, proper integral `q : Y ⟶ Spec R`, and supplied
isomorphism `e` between their literal generic fibres. The original `X`
is regular of dimension at most two.
`exists_regular_commonDomination` gives a finite point-blowup chain
`β : W ⟶ X`, a second projection `γ : W ⟶ Y`, and the original graph
lift. The regular integral Noetherian `W` has dimension at most two and
proper flat structure map; both projections are proper, surjective and
birational. Their literal generic isomorphisms have the original native
base-change maps as forward arrows and satisfy `eX ≪≫ e = eY`. Compatible
supplied sections lift uniquely with both original projection equations,
using [proper trait sections](../../Morphisms/Proper/TraitSections.md).
Regularity of the original source is essential to this construction;
resolution from arbitrary singular initial data remains separate.

## Exceptional curves and point-blowup factorization

[ExceptionalConormal](ExceptionalConormal.md) proves nonvanishing of the
original canonical conormal map for a proper dominant birational morphism
and an actual compatible isomorphism of Cartier divisors. If both divisors
are projective lines over the same specified field and their actual
conormals have supplied native `O(1)` comparisons, that same canonical
map is an isomorphism. The ambient target is integral and locally
Noetherian; ambient regularity, normality and a dimension bound are not
required. Identifying different centre residue fields is a separate step
in the factorization proof.

[ExceptionalLocus](ExceptionalLocus.md) defines `contractedCurves f` using
actual irreducible closed curves and their original images. For an integral
Noetherian source of dimension at most two, an integral locally Noetherian
normal target, and a proper dominant `f` with invertible original
function-field map, this set is finite. With the same dimension bound on
the target, an empty set, or its zero finite count, forces `f` to be an
isomorphism. Factoring through an actual closed regular-point blowup
strictly decreases the finite count. The proof constructs a curve mapping
onto the whole exceptional divisor; it assumes no curve isomorphism.

[Factorization](Factorization.md) proves
`exists_pointBlowupChain_factorization` for a proper dominant morphism
`f : X ⟶ Y` between integral schemes with regular stalks and dimension at
most two, with `Y` Noetherian and the actual `functionFieldMap f`
invertible. Noetherianity of `X` follows from properness. It returns
`β : Z ⟶ Y`, a literal `Blowup.PointBlowupChain β`, and an explicit
`e : X ≅ Z` satisfying `e.hom ≫ β = f`. A wrapper accepts
`BirationalOver f (𝟙 Y)`. The proof constructs the lift through each bad
target-point blowup and terminates by the strict finite-count decrease.
There is no excellence, characteristic, perfectness or projectivity
assumption. Construction of a regular scheme from singular initial data
and minimal-model existence remain separate tasks.

## Normalized covers and finite domination

[NormalizedBlowupCover](NormalizedBlowupCover.md) constructs the literal
normalized blowup of a nonzero ideal over a domain and its original
invertible image ideal, including nonflat ideal-pullback frames.
[Finite](NormalizedBlowupCover/Finite.md) constructs the second normalization
in the original finite extension field and its B-structure.
[Nagata](NormalizedBlowupCover/Nagata.md) proves finiteness and properness
for these same objects over a Noetherian Nagata domain of dimension at most
two, without separability.
[FiniteDomination](FiniteDomination.md) constructs normal proper birational
models and an actual finite map dominating a supplied proper birational
upper model over the original finite injective algebra, with both base
squares and generic maps retained. Its coefficient row and projective
factorization are constructed, not assumed. The finite separable H1 bound
consumes this diagram; separability is needed there for the discriminant,
not for this domination construction.
