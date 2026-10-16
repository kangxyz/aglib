# Native resolution-section comparisons

[Derived](Derived.lean), imported as
`Aglib.AlgebraicGeometry.Cohomology.DirectImage.ResolutionSections.Derived`,
identifies homology of the installed bounded-below derived global sections
of the original degree-zero coefficient single with the unchanged additive
`Sheaf.H`. For an arbitrary commutative ring and scheme in universe `u`,
`moduleDerivedGlobalSectionsSingleCohomologyLinearEquiv X α I n` is linear
over the specified map `α : R →+* Γ(X, ⊤)` and retains original cohomology
in universe `u + 1`. Its supplied-model comparison is homology of the
original resolution/derived-unit isomorphism inverse followed by native
`homologyFunctorFactors`. The `_model` and `_homologyπ` formulas retain
that exact model and its original resolution-cycle Ext class. Naturality
holds for every actual coefficient-resolution lift and uses the original
`moduleCohomologyMapOfHom`; `_eq` proves independence of the supplied
resolution. These comparisons require no quasicoherence, flatness,
Noetherianity or finiteness and introduce no global categorical instance.

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
