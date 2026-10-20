# Affine coordinates and actual scalar maps

[AlgebraMapTriangles](AlgebraMapTriangles.lean) owns
`AlgebraicGeometry.Spec.map_algHom_algebraMap`: the spectrum of an actual
algebra homomorphism commutes with the original scalar maps. It requires only
commutative rings and the two specified algebra structures. The three historical
coefficient/DVR/node structural triangles share this implementation.
[StructureMap](StructureMap.lean) uses native `Spec.algebraMap` and proves its
locally finite-type property for a finite-type algebra over a field.

[TensorPullback](TensorPullback.lean) provides
`Spec.isPullback_of_tensorEquiv` for an actual `S ⊗[R] A ≃ₐ[S] B` together
with the specified right-factor map `A →+* B`. The displayed pullback has
exactly those algebra maps; an unrelated spectrum isomorphism is insufficient.
[IsomorphismCoordinates](IsomorphismCoordinates.lean) provides
`Spec.ringEquivOfIso` and `Spec.algEquivOfIso`; the latter retains the supplied
triangle over `Spec R`, and their spectrum maps are the original inverse arrow.

[BaseChangeCoordinates](BaseChangeCoordinates.lean) uses
`Scheme.AffineBaseChange`. For an actual affine `X : Over (Spec R)`, its
`coordinateAlgebra` is induced by `X.hom.appTop`. `tensorSpecIso` identifies
`Spec (Γ(X.left, ⊤) ⊗[R] S)` with the literal base change, and its two
projection equations retain the left/right tensor inclusions and `X.isoSpec`.
`tensorSpecIso_naturality` and its inverse form concern the actual right-factor
algebra homomorphism. `coordinate_flat` additionally requires `Flat X.hom`.

[FieldSections](FieldSections.lean) provides
`Spec.affineFieldSectionEquiv` and its map formula for arbitrary commutative
algebras over a field and field-valued sections in the same universe. There is
no finite or étale hypothesis on the algebra. The spectrum functor is the
existing `Scheme.FiniteEtale.algebraSpecOver`; its native finite-étale fibre
comparison remains the finite-étale specialization.

The incoming source is the frozen R5 packet at
`f8a3314ddecffcada2ec721d26d56a937bed9690`; each leaf records its exact source
hash. Existing Aglib interfaces at `3a4d549` are preserved. The immediate
consumers are finite-étale adic lifting and affine coordinate calculations.
