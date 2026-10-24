# The original chosen-embedding trace on canonical sections

[Trace.lean](Trace.lean) transports the existing source-local trace through
the actual concentration isomorphism. Its canonical module is literally
`normalSurfaceCanonicalModule`, the degree-n homology of
`normalSurfaceDualizingObject`. The ambient coefficient remains
`normalSurfaceAmbientCoefficient`, the original top-differential
coefficient functor at the structure unit.

The assumptions are exactly those of the concentration supplier: a
regular local domain R, a normal integral source of dimension at most two,
the actual closed immersion into projective space, dominance over R,
and finiteness of the original function-field map. The source need not be
regular, the canonical module need not be invertible, and inseparability
and projective relative dimension zero remain allowed.

`normalSurfaceCanonicalShiftIso` is the actual
`normalSurfaceCanonicalIso`, included in the full derived category and
shifted by n, followed by the native `single_n(omega)[n] ≅ single_0(omega)`
comparison. The lower canonical isomorphism is normalized to the identity
on its original degree-n homology.

`normalSurfaceCanonicalSectionsAddEquiv` is an actual equivalence

    Gamma(X, omega_X) ≃ Hom_D(X)(O_X[0], K[n]).

For a section s, its forward map is the native structure-module morphism
corresponding to s, followed by the single functor and the inverse of
that same canonical-and-shift comparison. Its inverse takes the native
single preimage and evaluates the resulting coefficient morphism at one.
The application, inverse-application and normalization theorems display
these original maps explicitly.

`normalSurfaceCanonicalSectionsLinearEquiv` equips this same forward map
with linearity for any actual structural map `A → Gamma(X,O_X)`.
The section action is the native module action restricted through that
map. The scalar theorem identifies its image with precomposition by the
original multiplication endomorphism of the structure module.

For the original `sigma : R → A` and `g : X → Spec A`, the actual triangle
`i ≫ toSpec = g ≫ Spec.map sigma` derives the structural compatibility
through the original GammaSpec naturality. No map A→R or trace-compatibility
hypothesis is introduced. The intended finite injective local sigma and
proper birational g are retained as the supplied maps; these additional
properties are not needed for the trace transport itself.

`normalSurfaceSectionsTraceCoinduced` is the existing
`chosenEmbeddingTraceCoinduced` composed with this exact section
equivalence. It is A-linear into the original native coefficient
`(ModuleCat.coextendScalars sigma).obj (ModuleCat.of R R)`.
Its evaluation theorem proves

    Tr_A(s)(a) = Tr_R(a • s).

The output scalar law is the native coinduction action
`(a • phi)(b) = phi(b*a)`. The base trace also retains R-linearity for
the action restricted through sigma.

`normalSurfaceSectionsPhi0` uses the same source-local Phi0 after the
same section lift. `normalSurfaceSectionsTraceCoinduced_eq_original_unit`
identifies the section trace with this Phi0 after restriction of the
original `moduleDerivedStructureUnit`, displaying the native exact-single
normalization. The source-local supplier already derives its geometric
unit, section, counit and affine target comparisons.

This leaf establishes the section transport and its original-map trace
equations. It does not identify a newly selected cochain or Postnikov
model with that source, assert an embedding-independent proper/finite
trace identity, or prove GR vanishing. A GR/B7 consumer still has to use
the original supplied resolution and augmentation comparisons to identify
its concrete dual-complex map and perform its vanishing argument.
Existing coherent closed-embedding Serre duality is not replaced here.

The scalar-compatibility and base-trace restricted-scalar theorems
explicitly retain the original scheme triangle `hg` after `g`.
Their existing callers supply this triangle. The source-local base-trace
scalar theorem likewise retains its original `hα`; these corrections
restore the intended structural hypotheses in the theorem signatures.

The structure unit O and canonical module omega are objects of X.Modules.
Fully faithful additive and linear transports carry the same section
morphism through the original single functor and target isomorphism.
The scalar map alpha remains explicit; the output scalar law uses the
coinduced trace linear map’s `map_smul` equation on the restricted input.
No trace-compatibility premise is introduced.

Scalar transport and coinduced-trace evaluation use the proved equality
between the original linear and additive section maps. The trace factors
are the original canonical and structural comparisons.
