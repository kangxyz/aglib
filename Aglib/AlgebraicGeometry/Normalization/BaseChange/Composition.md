# Pasting normalization base change

Source: [Composition.lean](Composition.lean).

`Scheme.Hom.normalizationPullback_isIso_comp` applies to a qcqs morphism
`f : X ⟶ S` and composable base maps `g : Y ⟶ S`, `h : Z ⟶ Y`.
It assumes invertibility of the two actual successive native normalization
comparisons and concludes invertibility for the composite base map.

The proof compares the maps using the universal property of relative
normalization. The isomorphism between the iterated and composite original
pullbacks is `pullbackLeftPullbackSndIso`; `normalizationSourceIso` retains its
original structural equation. The same associativity isomorphism is used
on the normalized side. Both target projections and the original-source
comparison are checked before cancelling the source normalization isomorphism.

This categorical composition theorem does not supply compatibility with an
arbitrary flat base map. Its intended consumer combines proved affine
localization comparison with the existing open-immersion comparison.

Direct consumers: [AlgebraicGeometry/Normalization/BaseChange/Stalk](Stalk.md).
