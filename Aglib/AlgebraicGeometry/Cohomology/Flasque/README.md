# Flasque module sheaves and direct-image acyclicity

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.Cohomology.Flasque.Basic`, supplies the actual module-resolution/flasque section-surjectivity and kernel interfaces. Flasqueness is a property of the genuine coefficient presheaf; the successive resolution kernels retain the source's exact-sequence data.

[Pushforward](Pushforward.lean) gives `AlgebraicGeometry.Scheme.Modules.isZero_rightDerived_pushforward_succ_of_flasque`. For an arbitrary scheme morphism and coefficients whose actual presheaf is flasque, every positive right-derived direct-image object vanishes. No affine-morphism or quasicoherence premise is required for this result.

The lower subjects are actual stalk/section functors and [resolution kernel sequences](../../../CategoryTheory/Abelian/Injective/README.md). Affine additive comparison and the actual first-cohomology direct-image comparison consume these interfaces. The separate affine-quasicoherent acyclicity theorem has its own [Affine](../Affine/README.md) owner.

[Complex](Complex.lean) and [PushforwardExactness](PushforwardExactness.lean) preserve the original actual-complex flasque/kernel conditions, including quasi-isomorphism/direct-image comparisons and short exactness with flasque kernel. [Extensions](Extensions.lean) derives flasqueness from the stated actual short exact outer terms.

[DerivedPushforward](DerivedPushforward.lean) gives `isIso_derivedPushforwardPlusUnit_of_flasque` for a bounded-below complex whose every term is flasque. [LocalDerivedPushforward](LocalDerivedPushforward.lean) keeps an actual jointly covering family of open immersions into the target and flasqueness of every term after restriction to its pullbacks; under those premises the original derived direct-image unit is invertible. Neither result assumes that raw pushforward preserves every quasi-isomorphism.
