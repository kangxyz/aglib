# Exactness detected by the original homology mate

[Exactness](Exactness.lean) defines the native cycle sequence
`S.cycles → S.X₂ → S.X₃` and its canonical map from `S`, which fixes the
middle and last objects. The sequence is exact by the original cycles'
kernel universal property.

`Adjunction.exact_map_cyclesShortComplex_of_epi_homologyComparison` assumes
an additive adjunction between abelian categories whose right adjoint
preserves homology. An epimorphism of the original homology comparison
implies exactness after applying the left adjoint to this actual sequence.
The proof uses coefficient naturality of the unchanged mate and the native
homology map. Kernel or homology preservation by the left adjoint,
finiteness and boundedness are not premises. The current consumer is the
pointwise scalar-extension/base-change criterion.

[Counit](Counit.lean) constructs `Adjunction.homologyCounit` and its ordinary
adjunction mate `homologyCounitMate` for additive functors whose left adjoint
preserves homology. The mate starts with the original unit at
`(S.map G).homology`. `cyclesCounitMate_iCycles` and
`homologyCounitMate_homologyπ` retain the actual cycle inclusion and class
projection; `map_homologyCounitMate_counit` recovers the original counit
homology map. No homology preservation by the right adjoint or invertibility
of the counit is needed. These equations supply the affine section-counit
normalization.

[Reflection](Reflection.lean) treats an additive adjunction with invertible
counit and homology-preserving left adjoint. `reflectedHomologyIso` identifies
the reflection of the original included homology with original homology in
the reflective category. `homologyReflectionUnit` delegates to the canonical
`homologyCounitMate` and retains its original invertible-counit argument. Its
actual adjunction-unit/isomorphism formula remains definitionally unchanged. Coefficient naturality and the original
unit/counit equation are explicit, and reflecting this unit gives an
isomorphism. Homology preservation by the right adjoint is not a premise.
Native module-sheaf sheafification is the current consumer.

[Cycles](Cycles.lean) defines `Adjunction.cyclesUnit` through the original
unit and native exact right-adjoint cycle comparisons. Its inclusion and
projection equations retain the actual `iCycles`, `homologyπ` and original
`homologyUnit`. Following any actual `δ : S.map F ⟶ T` gives
`cyclesUnitMap`; `homologyComparison_map_homologyπ` computes the existing
canonical homology mate followed by the actual homology map on those
original cycle classes. The right adjoint preserves homology, and the left
adjoint need not be exact. Native scalar extension of resolution sections
is the current consumer, including its unit pure-tensor formula without
scalar flatness.

The cycle/projection normalization in `Cycles` delegates to the sole native
[MapHomology/Components](../MapHomology/Components.lean) owner. Its original
right-adjoint homology-preservation guard remains unchanged.
