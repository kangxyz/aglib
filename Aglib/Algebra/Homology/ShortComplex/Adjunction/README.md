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

[Reflection](Reflection.lean) treats an additive adjunction with invertible
counit and homology-preserving left adjoint. `reflectedHomologyIso` identifies
the reflection of the original included homology with original homology in
the reflective category. `homologyReflectionUnit` uses the actual adjunction
unit followed by that isomorphism. Coefficient naturality and the original
unit/counit equation are explicit, and reflecting this unit gives an
isomorphism. Homology preservation by the right adjoint is not a premise.
Native module-sheaf sheafification is the current consumer.
