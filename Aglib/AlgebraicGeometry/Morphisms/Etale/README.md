# Etale stalk maps and neighborhoods

[StalkMap](StalkMap.lean), imported as `Aglib.AlgebraicGeometry.Morphisms.Etale.StalkMap`, gives `AlgebraicGeometry.Scheme.stalkMap_essentiallyEtaleProperties` and the actual maximal-ideal lying-over comparison for an etale scheme morphism. Its commutative local-ring algebra is the original stalk map.

[StalkBaseChange](StalkBaseChange.lean) uses the lower [formal-etale ring-map operations](../../../RingTheory/Etale/README.md), proves `Scheme.LocalRing.Etale.etale_stalkMap_formallyEtale` for an actual etale morphism and `fromSpecStalk_flat` for the canonical target localization, and constructs `Scheme.LocalRing.Etale.stalkMapIsoOfIsPullbackOfFlatOfPreimmersion` for an actual supplied pullback square with flat preimmersion base map. `stalkMap_formallyEtale_of_etale_stalkBaseChange` recovers formal etaleness of the original stalk map from the actual base change to the target stalk.

[Locus](Locus.lean) gives `Scheme.LocalRing.Etale.exists_etale_neighborhood_of_stalkMap_formallyEtale`: a locally finitely presented morphism, a specified point and formal etaleness of its stalk map yield an etale open neighborhood. The locally finite-presentation premise remains essential. The etale-stalk-base-change variant has the same neighborhood conclusion.

The focused imports are these three leaves. Lower [essentially etale local algebra](../../../RingTheory/RegularLocalRing/README.md) and actual [scheme stalks](../../Stalk/README.md) feed [smooth regularity/dimension](../Smooth/README.md) and local etale consumers. Objects are arbitrary schemes in the declared universe.
