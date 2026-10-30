# Limits, colimits and preservation

[NatTransCoproduct](NatTransCoproduct.lean), imported as `Aglib.CategoryTheory.Limits.NatTransCoproduct`, gives `CategoryTheory.NatTrans.isIso_app_coproduct` for the actual coproduct comparison with the source's preservation and componentwise-isomorphism hypotheses. [FiniteCoproductFunctor](../Abelian/FiniteCoproductFunctor.lean) separately supplies finite-limit/finite-colimit preservation of finite coproducts in the abelian setting.

`CategoryTheory.Limits.IsPushout.isSplitMono_inr` is the generic split-pushout result in [DegreewiseSplitMono](../../Algebra/Homology/CochainComplex/DegreewiseSplitMono.lean): in an arbitrary category, a chosen pushout square with split first input has split opposite inclusion. No abelian structure is needed for this lower square statement.

Finite-free sheaf tensors and degreewise split cochain pushout arguments consume these actual universal-property maps. Product/coproduct index and universe hypotheses are preserved by each source statement.

[BiproductPushout](BiproductPushout.lean), imported as `Aglib.CategoryTheory.Limits.BiproductPushout`, proves `CategoryTheory.Limits.IsPushout.biprod_map`: the literal biproduct maps of two displayed pushout squares form a pushout in a preadditive category with binary biproducts. No mono or splitting premise is required. [Shapes](Shapes/README.md) owns displayed cokernel-to-pushout and zero-coproduct results. The [identity-cone functor](../../Algebra/Homology/MappingCone/README.md) consumes these universal-property primitives.

[FullSubcategory](FullSubcategory/README.md) lifts a displayed ambient pushout to the actual full-subcategory functor once every value, including the chosen apex, satisfies the object property. [SequentialSystem](Shapes/SequentialSystem/README.md) constructs colimits of sequences of isomorphisms, finite-tail comparisons and invertibility of the original stage inclusions for eventually invertible sequences. Its sign-correction leaf turns anti-commuting successor squares into natural transformations with the prescribed alternating components. These categorical results retain only their stated colimit, isomorphism or preadditivity hypotheses.

[Types/NatTower](Types/NatTower.lean) proves that adjacent compatibility
implies compatibility for every arrow in a natural-number inverse tower,
and that every stage evaluation on native sections is surjective if all
adjacent maps are surjective. It uses dependent choice along the prescribed
tail, without introducing a second limit construction.

[FiniteCoproductMaps](FiniteCoproductMaps.lean), imported as
`Aglib.CategoryTheory.Limits.FiniteCoproductMaps`, gives
`CategoryTheory.Limits.Sigma.desc_induction`: in a category with finite coproducts, a property of
morphisms into a fixed object that is stable under precomposition with isomorphisms, holds on
initial objects and is stable under binary `coprod.desc` holds for `Sigma.desc` over every finite
index type (through `sigmaOptionIso : Y none ⨿ ∐ (Y ∘ some) ≅ ∐ Y`).
`CategoryTheory.FinitaryExtensive.isPullback_sigmaι_sigmaMap` shows that summand inclusions are
cartesian over `Sigma.map f` in a finitary extensive category. Consumer: the finite disjoint unions
of H-quasi-projective schemes
([ProjectiveSpace/QuasiProjective/Coproduct](../../AlgebraicGeometry/ProjectiveSpace/QuasiProjective/Coproduct.lean)),
through `Sigma.desc_induction`.

[JointConservativity](Preserves/JointConservativity.lean) proves colimit
preservation for the actual supplied functor using a family that jointly
reflects isomorphisms, with the stated target-colimit and preservation
hypotheses. The index and category universes remain independent.
[PresheafSections](Preserves/PresheafSections.lean) proves that the original
abelian-valued presheaf cocone is colimiting from joint surjectivity and
eventual equality. Its independent index, category and value universes retain
the displayed size bounds; the original presheaf maps and cocone legs are used.

[ConeTriangle](ConeTriangle.lean) transports the supplied contravariant cocone
along its actual cone triangle and evaluates the resulting cone directly.
[OverChartTransitions](OverChartTransitions.lean) constructs the original
property-Over charts and their transition values.
[CoconeValues](CoconeValues.lean) keeps the supplied cocone and legs for zero
detection, filtered representatives and relations, and naturality of uniqueness
isomorphisms. Each theorem retains its stated colimit, preservation or
filteredness hypotheses.
