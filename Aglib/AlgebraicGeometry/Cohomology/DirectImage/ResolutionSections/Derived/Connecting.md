# Original sections and connecting maps of derived global sections

`moduleDerivedGlobalSections_homology_zero_sections` identifies the
original supplied-resolution comparison with the original degree-zero
section normalization. Its proof uses the H0 normalization
of `Proper/DerivedStructure`: the native inverse R0 comparison is the
actual augmentation cycle, whose original Ext class is `Ext.mk₀` of the
same section morphism.

`moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_extAction`
evaluates an original degree-one Ext class on the same native R0 section.
The proof uses the supplied target resolution, its actual shifted cocycle,
the installed native derived unit, and the original resolution model.
Native cycle projection and shift formulas identify the resulting class
with the original Yoneda product. Neither the section carrier nor its
specified scalar action changes.

`moduleDerivedGlobalSectionsConnectingOfHom` is the actual degree-zero to
degree-one homology boundary of the original short-exact single triangle
after applying the installed derived global-sections functor.
`moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv_connecting`
identifies that boundary with the original
`moduleCohomologyConnectingOfHom`. The original `Ext.homPlus_extClass` and
`moduleExtCohomologyMap_connectingOfHom` formulas retain the positive sign.

The coefficients are arbitrary module sheaves. No flatness, quasicoherence,
finiteness or exactness of global sections is assumed. The current consumer
is the original proper-birational Leray map comparison in
`Cohomology/Proper/DerivedStructure`.
