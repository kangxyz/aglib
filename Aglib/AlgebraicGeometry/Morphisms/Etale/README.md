# Etale stalk maps and neighborhoods

[StalkMap](StalkMap.lean), imported as `Aglib.AlgebraicGeometry.Morphisms.Etale.StalkMap`, gives `Scheme.stalkMap_essentiallyEtaleProperties` under local finite type, flatness and formal unramifiedness. Its dimension and regularity comparisons concern the actual stalk map and retain the target-stalk Noetherian or regular-local hypothesis. The arbitrary-map maximal-ideal and finite-type Noetherian helpers live in [Stalk/MapProperties](../../Stalk/MapProperties.lean).

[StalkBaseChange](StalkBaseChange.lean) uses the lower [formal-etale ring operations](../../../RingTheory/Etale/README.md) and [flat stalk comparisons](../../Stalk/FlatBaseChange.lean). It proves `Scheme.LocalRing.Etale.etale_stalkMap_formallyEtale` for an actual etale morphism. `stalkMap_formallyEtale_of_etale_stalkBaseChange` recovers formal etaleness of the original stalk map from the actual base change to the target stalk. No flatness premise is added to the original morphism.

[Locus](Locus.lean) gives `Scheme.LocalRing.Etale.exists_etale_neighborhood_of_stalkMap_formallyEtale`: local finite presentation, a specified point and formal etaleness of its stalk map give an etale open neighborhood. The base-change variant retains the same local finite-presentation hypothesis.

These three focused imports extend native Mathlib etale morphisms. Lower [essentially etale local algebra](../../../RingTheory/RegularLocalRing/README.md) and the original [scheme stalks](../../Stalk/README.md) feed [smooth regularity/dimension](../Smooth/README.md). The arbitrary-scheme flat/localization and stalk-map properties retain their lower stalk owners.
