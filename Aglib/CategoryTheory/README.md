# Categorical structures and generic cohomological support

[ExactCategory](ExactCategory/README.md) adds a selected-conflation exact structure and exact functors in `CategoryTheory.ExactCategory`. [Abelian](Abelian/README.md) contains genuine object-property subcategories and supplied injective-resolution/Ext-map comparison. [SmallModel](SmallModel/README.md) transports actual additive, abelian and exact structure under the stated essential-smallness witness.

[Site sheaf cohomology](Sites/SheafCohomology/README.md) contains generic Cech complexes and their actual coefficient/section comparisons. [Topological sheaves](../Topology/Sheaves/README.md) is the lower owner for topological section complexes and basis detection. Scheme specialization belongs to [AlgebraicGeometry/Cohomology](../AlgebraicGeometry/Cohomology/README.md).

The principal categorical results are preservation/transport of actual conflations, abelian subcategory construction from explicit closure conditions, exact kernel sequences of a supplied resolution and split-cover Cech exactness. Restricted-open Cech comparisons belong to [topological Cech theory](../Topology/Sheaves/Cech/README.md). Their guides distinguish structures constructed from supplied data from separate existence assertions.

[Triangulated](Triangulated/README.md), [Adjunction](Adjunction/README.md), [Limits](Limits/README.md) and [NatTrans](NatTrans/README.md) add the generic triangle, mate, coproduct and unit comparisons used by bounded derived/Godement calculations. Their hypotheses remain categorical until a scheme consumer supplies the geometric data.

[Monoidal](Monoidal/README.md) adds the additive braided and symmetric structures on `Discrete M` and multiplication by a morphism out of the tensor unit, with its coherence for lax monoidal and lax braided functors. Its first consumer is the braided twisting functor of projective space.

[Preadditive](Preadditive/README.md) collects coproduct facts in preadditive categories: sums of projection–inclusion composites, decomposition of morphisms out of a coproduct and zero objects of bilimits.

The [Pi family](Pi/README.md) contains dependent pointwise abelian structures and the
generic finite-object-support Serre subcategory. [PresentationColimit](PresentationColimit.lean) constructs
functorial colimits over the actual costructured presentation category and their
universal natural comparison; it asserts no comparison-isomorphism theorem.
[Galois.Connected](Galois/Connected.lean) transports connected objects under equivalences.
[Grp](Grp.lean) provides an explicit underlying-object composition formula. [Iso.Composite](Iso/Composite.lean)
provides endpoint equality transport, while cancellation and reassociation use
the existing Mathlib API.

Focused interface guides: [Effective epimorphisms over a base](EffectiveEpi/README.md).

[ObjectProperty/Yoneda](ObjectProperty/Yoneda.lean) tests morphisms on the objects of a property
`P`: `ObjectProperty.isIso_of_yoneda_map_bijective` (bijective on `T`-points for `P T`, with `P X`
and `P Y`, gives an isomorphism) and `ObjectProperty.mono_of_yoneda_map_injective` (injective on
`P`-points with `P (X ×_Y X)` gives a monomorphism, through `fst_eq_snd_…` and
`isIso_diagonal_…`); Stacks 001P and 08LR in the full subcategory of `P`.
[ObjectProperty/EquivalenceRelation](ObjectProperty/EquivalenceRelation.lean) defines
`pointsRelation p₁ p₂ T` (the image of `R(T) → X(T) × X(T)`) and compares Mathlib's internal
`EquivalenceRelation` with it: internal relations give equivalence relations on all points
(`EquivalenceRelation.equivalence_pointsRelation`), and for jointly monic `p₁, p₂` with `P X`,
`P R`, `P (R ×_X R)` the converse holds from `P`-points (`ObjectProperty.equivalenceRelationOfPoints`,
`ObjectProperty.isEquivalenceRelation_iff_points`). Over a base: `Over.pointsRelation_iff`,
`Over.equivalence_pointsRelation_iff`, `Over.jointlyMono₂_of_left`; joint monicity from a
monomorphism: `jointlyMono₂_comp_of_mono`, `jointlyMono₂_pullback_fst_snd`. Consumer: the locally
Noetherian tests of `AlgebraicGeometry/Properties/Noetherian`.

[ObjectProperty/RepresentableBy](ObjectProperty/RepresentableBy.lean) restricts representations to
full subcategories: `Functor.FullyFaithful.representableBy` turns `F.RepresentableBy (G.obj Y)` into
`(G.op ⋙ F).RepresentableBy Y` for fully faithful `G` (values in any universe), and
`ObjectProperty.representableByιOfLE` does so along `ObjectProperty.ιOfLE` for `P ≤ Q`.
[ObjectProperty/GrpObj](ObjectProperty/GrpObj.lean): for `P` closed under the terminal object and
binary products in a cartesian monoidal `C` (Mathlib's `CartesianMonoidalCategory.fullSubcategory`),
`MonObj.ofFullSubcategory`, `GrpObj.ofFullSubcategory`, `IsCommMonObj.ofFullSubcategory` and
`CommGrpObj.ofFullSubcategory` carry a (commutative) monoid or group object `X` of
`P.FullSubcategory` to `X.obj`, with the same unit, multiplication and inverse (by definition); the
braidings of `C` and of `P.FullSubcategory` agree (`ObjectProperty.braiding_hom_hom`). These are
definitions, not instances. Consumer:
[Sites/OverRepresentability/CommGrpObj](../AlgebraicGeometry/Sites/OverRepresentability/CommGrpObj.lean).
