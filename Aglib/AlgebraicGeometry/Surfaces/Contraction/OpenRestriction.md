# The exceptional curve in an actual open neighbourhood

`Surfaces.Contraction.exists_exceptional_in_open` constructs the local
exceptional input for proper-map contraction. It starts with the original
closed immersion `i : P¹_k ⟶ X`, an actual open immersion `j : U ⟶ X`, and
`range i ⊆ range j`. The original kernel ideal is assumed locally of rank
one, and its pullback to the same `P¹_k` is supplied with an actual `O(1)`
isomorphism. The result gives the immersion into the unchanged `U`, its
original triangle, a cartesian square with identity on `P¹_k`, local rank
one of its kernel ideal, and the retained `O(1)` conormal isomorphism.

The map is the native `IsOpenImmersion.lift`, exposed as
`OpenRestriction.map`. `map_comp` retains `iU ≫ j = i`, and `isPullback`
proves the displayed square cartesian. Closedness follows by base change.
The construction preserves the original curve, its full field `k`, the
specified open scheme and the ambient map.

`OpenRestriction.idealPullbackMap_isIso` applies the existing
`Scheme.Hom.idealPullbackMap_isIso_of_isOpenImmersion` to that square.
`idealIso` is the resulting isomorphism whose forward map is precisely
`Hom.idealPullbackMap i iU j (𝟙 _)`; `idealIso_hom_inclusion` records its
compatibility with the original ideal inclusions. Pullback preserves local
rank one, which supplies `isLocallyRankOne_ideal` and `idealLine`.
`conormalIso` then uses this canonical map, the native pullback composition
isomorphism and the original triangle. `conormalTwistIso` composes it with
the supplied `O(1)` comparison on the same projective line.

The generic helpers accept any original source scheme. `ker_comap` identifies
the full pulled-back kernel ideal, `range_map` gives the exact preimage of
the original curve, and `preimage_complement` gives the corresponding
complement formula. These statements use the original morphisms rather than
an independently chosen isomorphic curve or neighbourhood.

This module constructs the open restriction only. The proper-map consumer
chooses `U`, proves the range containment, and separately supplies the
projective presentation used by the contraction kernel. No properness or
projectivity theorem, residue-field equality, or additional regularity
hypothesis is introduced here. Compilation is coordinated with that consumer;
the source and this guide are not separate validation evidence.
