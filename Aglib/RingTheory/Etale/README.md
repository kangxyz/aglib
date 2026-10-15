# Formal etaleness of actual ring maps

[FormalProperties](FormalProperties.lean), imported as `Aglib.RingTheory.Etale.FormalProperties`, extends `RingHom.FormallyEtale` for actual homomorphisms of commutative rings in the same universe. `iff_formallyUnramified_and_formallySmooth` identifies the formal property with those two algebra-level conditions.

`RingHom.FormallyEtale.stableUnderComposition`, `respectsIso`, `isStableUnderBaseChange` and `holdsForLocalization` supply the corresponding ring-property interfaces. `RingHom.FormallyEtale.localRingHom` preserves formal etaleness for the canonical map between prime localizations, with the actual prime ideals, their prime instances and the equality relating their comap. `RingHom.Etale.formallyEtale` forgets the finite-presentation part of etaleness.

The prime-localization statement concludes formal etaleness. It does not assert finite presentation or etaleness of that localized map. [Scheme stalk etale base change](../../AlgebraicGeometry/Morphisms/Etale/README.md) consumes these generic ring-map operations; their source's scheme application is provenance rather than their mathematical owner. [Regular-local etale comparison](../RegularLocalRing/README.md) separately retains local Noetherian, flat and essentially-finite-type hypotheses for dimension and regularity.
