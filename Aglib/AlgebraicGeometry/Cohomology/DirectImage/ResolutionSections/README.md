# Native resolution-section comparisons

[Pullback](Pullback.lean), imported as
`Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Pullback`,
constructs `moduleResolutionPullbackSectionsTensorMap` from the actual
geometric unit, original supplied resolutions and their certified native
comparison. The native scalar adjunction supplies its tensor mate.
`moduleResolutionPullbackSectionsTensorMap_one_tmul` retains the original
unit and comparison component on every section. The actual mapped cycle is
identified with the original exact-functor Ext cocycle and original
unit-module precomposition. `moduleResolutionPullbackSectionClass` therefore
gives exactly the existing geometric cohomology map on original cycle
classes. These constructions and formulas require flat geometric pullback;
they require neither scalar flatness nor quasicoherence. The subsequent
tensor-homology comparison uses the same actual chain map and original
class maps. `moduleResolutionPullbackSectionsHomologyMap` is the existing
canonical scalar-extension homology mate followed by homology of that
actual section-complex map. Its `_homologyπ` formula retains the original
cycle projection, and its `_one_tmul` formula is exactly the original
geometric cohomology pullback through
`moduleResolutionSectionsCohomologyLinearEquiv`. These homology formulas
still require no scalar flatness or quasicoherence. Scalar flatness enters
the later invertibility argument.

The native section complexes, original cohomology equivalences and open,
coefficient and presheaf comparisons are documented in the
[owning direct-image guide](../README.md).
