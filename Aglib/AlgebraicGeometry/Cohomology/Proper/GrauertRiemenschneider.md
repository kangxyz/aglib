# Chosen-embedding complete-local surface GR

`Scheme.Cohomology.grauertRiemenschneider_chosenEmbedding` states
vanishing of the original degree-one sheaf cohomology of
`normalSurfaceCanonicalModule R iota i n`. This is the literal canonical
module of the supplied closed embedding; no invertibility or source
regularity is part of its definition or the theorem.

The geometric inputs are a proper dominant map `f : X → Spec A` from an
integral normal scheme of dimension at most two, an isomorphism on the
original function fields, and an actual closed embedding
`i : X → ProjectiveSpace R iota` with `iota ≃ Fin (n+1)` and
`i ≫ toSpec = f ≫ Spec.map sigma`. The ring R is a regular local domain
of dimension two. The ring A is a complete Noetherian normal local domain
of dimension two. The supplied map `sigma : R → A` is finite, injective
and local.

The public theorem chooses the actual injective resolutions of the
structure module and R internally. Its proof uses these same resolutions
through all comparisons:

1. The original proper birational map is an isomorphism away from the
   closed point. The actual punctured-spectrum restriction theorem and
   proper finite-length cohomology identify its original H1 as a
   finite-length A-module.
2. The finite local map transfers that same module to finite R-length
   through the native residue-degree length formula. Finite normal
   algebra freeness supplies projectivity of the original restricted
   A-module. These give the actual finite-projective model and original
   evaluation isomorphism at the derived structure object.
3. The actual residue module has finite restricted coefficients, hence
   its original evaluation is invertible. Its derived-dual comparison
   uses the same chosen R-resolution.
4. The original unit-Postnikov triangle gives dual amplitude [0,1] and
   finite-length intrinsic H1. Completeness makes A Nagata, so the actual
   residue-field morphism-vanishing theorem applies. The original
   evaluation naturality obstruction kills that top dual homology.
5. `normalSurfaceCohomologyDualLinearEquiv` in degree one transfers this
   vanishing to the original sheaf cohomology of the literal canonical
   module.

The function-field finiteness required by the chosen-embedding comparison
is also proved internally. The canonical generic-fibre isomorphism of
`Spec.map sigma`, followed by its finite second pullback projection,
identifies the actual function-field map as finite. Composition with the
original birational field isomorphism and the supplied factorization
proves finiteness of `genericImageBaseMap R iota i`. Its source is
`(Spec R).functionField`, and its original ring map is retained.

There is no final assumption of a perfect model, dual comparison,
trace compatibility, punctured isomorphism, generic field finiteness,
residue vanishing or finite-length scalar restriction. The helper with
supplied computational resolutions has a generic-finiteness argument
which the public theorem discharges. The degree-zero geometric trace
normalization is not used; that remains separate B7 work.

This theorem concerns the supplied closed embedding. It asserts neither
embedding independence nor construction of an embedding for an arbitrary
proper surface model.
