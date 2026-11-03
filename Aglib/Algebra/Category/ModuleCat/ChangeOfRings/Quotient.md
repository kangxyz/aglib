# Native scalar extension of quotient sources

Source: [Quotient.lean](Quotient.lean).

`quotientScalarExtensionIso_one_tmul` records the unit formula of the original
`extendScalarsAlgebraObjIso` composed with the inverse original
`quotIdealMapEquivTensorQuot`. It does not define a new quotient model.

`quotientScalarExtensionIso_comp` compares two successive original scalar
extensions with their composite, using native `extendScalarsComp` and the
canonical quotient equivalence for `Ideal.map_map`. Its statement retains the
actual source quotient and actual mapped ideals. All rings are arbitrary
commutative rings; no field, flatness, finiteness, or Noetherian assumption is
needed for these source equations.

This is the source leg needed by closed-adjoint flat overlap. The geometric
coefficient leg, exact-functor Ext comparison, actual restriction maps, and
sheaf gluing remain separate consumers. No compatibility or gluing theorem is
inferred solely from this algebraic composition.

## Inverse source comparison

`quotientScalarExtensionIso_inv_comp` derives the inverse-source equation from
`quotientScalarExtensionIso_comp` by cancellation of the same native
isomorphisms. Its mapped-ideal factor is the inverse of the original
`Ideal.map_map` quotient isomorphism; its scalar factor remains the original
`extendScalarsComp`. The ring actions are the same explicit `RingHom.toAlgebra`
actions. No flatness or finiteness premise is added.

This is the source equation consumed by the existing upstream
`Functor.extCoefficientTransfer_comp_of_eq`. Its geometric consumer must also
supply the proved original affine coefficient square; the inverse-source law
alone does not establish canonical-sheaf base change or overlap compatibility.

Direct consumers: [AlgebraicGeometry/Cohomology/ClosedImmersion/RightAdjoint/FlatBaseChange/SourcePresentation](../../../../AlgebraicGeometry/Cohomology/ClosedImmersion/RightAdjoint/FlatBaseChange/SourcePresentation.md).
