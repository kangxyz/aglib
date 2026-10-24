# Noetherian scheme geometry

[DenseAffine](DenseAffine.lean) is a compatibility import of the sole
[general dense-affine owner](../DenseAffine.lean), documented in the
[parent property guide](../README.md). All four original native `Scheme`
declaration names remain available.

The primitive affine enlargement and dense-neighborhood statements require
only finitely many irreducible components. Compactness additionally gives
the finite dense-affine cover and dense common intersection.
`Scheme.exists_finite_dense_affine_cover` retains its actual `IsNoetherian X`
hypothesis and follows from those general statements. The broader owner
records these weakest hypotheses without classifying the primitive results
as Noetherian-only geometry; empty schemes are still included.

[LocallyNoetherianOver](LocallyNoetherianOver.lean): `Scheme.LocallyNoetherianOver S`, the full
subcategory of `Over S` on locally Noetherian schemes (all morphisms over `S`; property
`Scheme.locallyNoetherianOver S`), with inclusion `Scheme.locallyNoetherianOverInclusion` and the
instance `Scheme.LocallyNoetherianOver.isLocallyNoetherian`: the test schemes of Nitsure,
*Construction of Hilbert and Quot schemes*, arXiv:math/0504590v1, §1, pp. 3–4.

[Coproduct](Coproduct.lean): a disjoint union of locally Noetherian schemes, over a small index type
in any universe, is locally Noetherian (`isLocallyNoetherian_sigma`, through Mathlib's
`sigmaOpenCover` and `isLocallyNoetherian_iff_openCover`), and
`Scheme.LocallyNoetherianOver.sigma H` is the disjoint union of locally Noetherian test schemes over
`S`, with structure morphism `Sigma.desc fun j => (H j).obj.hom` and inclusions
`LocallyNoetherianOver.sigmaι`. Consumer:
[HilbertScheme/Coproduct/Representability](../../HilbertScheme/Coproduct/Representability.lean);
H-quasi-projectivity of finite such unions over `Spec R` is
`Scheme.LocallyNoetherianOver.isHQuasiProjective_sigma_obj_hom`
([HilbertScheme/Coproduct/QuasiProjective](../../HilbertScheme/Coproduct/QuasiProjective.lean)).

[LocallyOfFiniteTypeOver](LocallyOfFiniteTypeOver.lean): `Scheme.locallyOfFiniteTypeOver S` (`T ⟶ S`
locally of finite type; Mathlib's `MorphismProperty.overObj @LocallyOfFiniteType` by
`locallyOfFiniteTypeOver_eq_overObj`) and its full subcategory `Scheme.LocallyOfFiniteTypeOver S`,
closed under isomorphisms, the terminal object and binary products (instances
`Scheme.isClosedUnderIsomorphisms_…`, `…_discrete_pEmpty_…`,
`Scheme.isClosedUnderBinaryProducts_…`), hence cartesian monoidal with the fibre products over `S`.
For `S` locally Noetherian, `Scheme.locallyOfFiniteTypeOver_le_locallyNoetherianOver` (Stacks 01T6),
the inclusion `Scheme.LocallyOfFiniteTypeOver.toLocallyNoetherianOver`, and the restriction of
representations `Scheme.LocallyNoetherianOver.representableByLocallyOfFiniteType`. Consumer: the
group law of
[Sites/OverRepresentability/CommGrpObj](../../Sites/OverRepresentability/CommGrpObj.lean).

[LocallyNoetherianOverBaseChange](LocallyNoetherianOverBaseChange.lean): for `g : S' ⟶ S`,
`Scheme.LocallyNoetherianOver.map g : LocallyNoetherianOver S' ⥤ LocallyNoetherianOver S` is
`Over.map g` on locally Noetherian test schemes (same underlying scheme;
`LocallyNoetherianOver.map_obj_obj`); for `S'` locally Noetherian and `Y ⟶ S` locally of finite
type, `(Over.pullback g).obj Y` is locally of finite type over `S'`
(`Scheme.locallyOfFiniteType_over_pullback_obj_hom`) with locally Noetherian source
(`Scheme.isLocallyNoetherian_over_pullback_obj_left`; Stacks 01T6), and
`Scheme.LocallyNoetherianOver.baseChange g P` is `P ×_S S'` as a locally Noetherian `S'`-scheme.
Consumer: [Picard/BaseChangeRepresentableBy](../../Picard/BaseChangeRepresentableBy.lean).

[Yoneda](Yoneda.lean): Yoneda on locally Noetherian test schemes. Isomorphisms
(`Scheme.isIso_of_locallyNoetherian_yoneda_map_bijective`; over `S`,
`Scheme.LocallyNoetherianOver.isIso_of_yoneda_map_bijective`, `isIso_left_…`), monomorphisms
through the diagonal under `IsLocallyNoetherian (X ×_Y X)` (`Scheme.mono_of_locallyNoetherian_yoneda_map_injective`,
`…_of_locallyOfFiniteType` for `Y` locally Noetherian and `f` locally of finite type; over `S`,
`Scheme.LocallyNoetherianOver.mono_{left_,}of_yoneda_map_injective`), proper and injective on
locally Noetherian points implies closed immersion
(`Scheme.isClosedImmersion_of_isProper_of_locallyNoetherian_yoneda_map_injective`, Nitsure p. 33),
factorization through closed subschemes (`Scheme.Hom.exists_lift_iff_ker_le_ker`,
`Scheme.IdealSheafData.exists_lift_subschemeι_iff_le_ker`, `…exists_lift_comap_subschemeι_iff`),
and equality of closed subschemes of a locally Noetherian scheme with the same locally Noetherian
points (`Scheme.Hom.ker_eq_of_locallyNoetherian_exists_lift_iff`,
`Scheme.IdealSheafData.eq_of_locallyNoetherian_exists_lift_iff`,
`…comap_eq_comap_of_locallyNoetherian_exists_lift_iff`). Consumers: F16 steps 1, 6, 7 (Nitsure,
proof of Thm 6.8, pp. 33–35) and F17 step 5 (`R ⟶ Z ×_S Z` a monomorphism, hence a closed
immersion; plan, Representability, step 5).

[EquivalenceRelation](EquivalenceRelation.lean): schematic equivalence relations (Nitsure §6, p. 31;
Stacks 022P) tested on locally Noetherian points:
`Scheme.isEquivalenceRelation_iff_locallyNoetherian_points` (jointly monic, `X`, `R`, `R ×_X R`
locally Noetherian), `…_of_locallyOfFiniteType`, `…_of_mono` (monomorphism `R ⟶ X ×_S X`, first
projection locally of finite type), `Scheme.isEquivalenceRelation_of_locallyNoetherian_points`
(no monicity: `S` locally Noetherian, `X ⟶ S` and `p₁` locally of finite type, injectivity on
points), and over `S` `Scheme.LocallyNoetherianOver.equivalence_pointsRelation_iff`,
`Scheme.LocallyNoetherianOver.isEquivalenceRelation_iff`. Consumer: the hypothesis of F16.

[LocallyConnected](LocallyConnected.lean): the instance
`AlgebraicGeometry.IsLocallyNoetherian.locallyConnectedSpace` (Stacks 04MF). The underlying space of
a locally Noetherian scheme is locally connected, because affine opens with Noetherian rings are
Noetherian spaces; so its connected components are open and closed (Mathlib's
`isClopen_connectedComponent`). Consumer: the identity component of a group scheme locally of finite
type over a field ([Group/IdentityComponent](../../Group/IdentityComponent/README.md)).
