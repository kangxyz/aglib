# Actual scheme stalks and local comparisons

[Dimension](Dimension.lean), imported as `Aglib.AlgebraicGeometry.Stalk.Dimension`, gives `Scheme.topologicalKrullDim_eq_iSup_stalk` for every scheme: its dimension is the supremum of its actual stalk dimensions. No field, Noetherianity or quasi-compactness is required.

[MapProperties](MapProperties.lean) gives `Scheme.stalkMap_maximalIdeal_liesOver` for every scheme map, using that map's induced algebra. `isNoetherianRing_stalk_of_locallyOfFiniteType` requires local finite type and Noetherianity of the target stalk, without a global Noetherian or etale hypothesis.

[FlatBaseChange](FlatBaseChange.lean) owns `Scheme.Hom.isIso_stalkMap_of_flat_of_surjectiveOnStalks`, `Scheme.fromSpecStalk_flat` and `Scheme.Hom.stalkMapIsoOfIsPullbackOfFlatOfPreimmersion`. The arrow isomorphism uses the supplied pullback square, flat preimmersion base map and actual point/equality. It compares the original stalk maps; no etale hypothesis is imposed.

[Polynomial](Polynomial.lean) gives actual polynomial-scheme stalk regularity, the all-prime dimension upper bound and the maximal-prime equality over an arbitrary field. [EtalePolynomial](EtalePolynomial.lean) supplies the corresponding three results for an actual etale map from that polynomial algebra. Dimension equality retains the maximal-ideal premise; no perfectness or separability is required. Its maximal-comap ring lemma belongs in [RingTheory/Etale](../../RingTheory/Etale/README.md).

[GenericFiber](GenericFiber.lean) retains `Scheme.LocalRing.GenericFiber` for the actual pullback of `p : Y ⟶ Spec A` to a supplied field `F` with `IsFractionRing A F`. Its projection's own stalk map gives `projection_stalkMap_isIso` and `stalkEquiv`. The general flat-stalk supplier is the lower `FlatBaseChange` interface; no global integrality condition on `Y` is added.

The lower stalk interfaces feed [etale transport and neighborhoods](../Morphisms/Etale/README.md) and [smooth regularity/dimension](../Morphisms/Smooth/README.md). Their focused imports separate arbitrary-scheme stalk theory from these stronger morphism specializations.

[IntegralExtension](IntegralExtension.lean) equates the dimensions of actual Spec stalks under an integral ring extension with going down, at the actual contracted prime. Its finite-product form retains the supplied algebra equivalence and both hypotheses on every factor. No domain, Noetherianity, dimension bound or finite-map hypothesis is added. [Generic finite-etale normalization dimensions](../Normalization/GenericFiniteEtale/Dimension.lean) apply this result to the actual integral-closure field factors.
