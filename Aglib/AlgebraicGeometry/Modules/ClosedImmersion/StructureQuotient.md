# The structure-module quotient of a closed immersion

For an arbitrary closed immersion `f : X ⟶ Y`,
`Scheme.Hom.structureModuleMap_epi` proves that the original morphism
`O_Y ⟶ f_* O_X` is an epimorphism of module sheaves.
`Scheme.Hom.idealSequence_shortExact` supplies the corresponding actual short
exact sequence

`0 ⟶ Hom.idealModule f ⟶ O_Y ⟶ f_* O_X ⟶ 0`.

The sequence is the native kernel sequence of `Hom.structureModuleMap f`.
Its first arrow is the existing `Hom.idealInclusion f`; no replacement ideal,
coefficient family or quotient comparison is assumed.

The proof reuses the existing
[`Scheme.Modules.pullbackPushforwardUnit_epi`](Unit.lean), which applies to
every module sheaf on `Y`. The structure-module endpoint follows through the
canonical pullback-unit isomorphism and its original adjunction equation.

These results require neither quasicoherence nor finite presentation,
Noetherianity, dimension, flatness or properness. They provide the untwisted
sequence used by Cartier-divisor cohomology; tensor exactness and the specific
restriction comparisons belong to their respective consumers.
