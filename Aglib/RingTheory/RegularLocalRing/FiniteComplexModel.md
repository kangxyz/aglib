# Finite-projective models over a regular local ring

For a regular local ring `R` with `ringKrullDim R = d`,
`IsRegularLocalRing.exists_finiteProjective_single_model` constructs a
complex of finite projective `R`-modules, supported in `[n-d,n]`, and an
actual quasi-isomorphism to the native single of any finite module `M` in
degree `n`. The ring lives in universe `u`; the module and final complex
live in `max u v`. Regularity includes the Noetherian and local hypotheses.

The construction first applies `Module.Finite.small` and the native
`Shrink.linearEquiv R M`. The existing projective-dimension bound and
finite minimal free resolution then apply in the ring universe. Their
actual augmentation is extended to integer degrees and mapped by the
exact native `ModuleCat.uliftFunctor`. The endpoint comparison is
`ULift.moduleEquiv` followed by `Shrink.linearEquiv R M`; these preserve
the original `R`-action. The degree-zero result is exposed separately as
`exists_finiteProjective_single_zero_model`.

Placement in degree `n` uses shift by `-n`, followed by the native
`singleFunctors.shiftIso (-n) n 0`. It therefore retains the original
augmentation and shift convention, rather than identifying the large
module with its shrink or replacing its action.

The immediate consumer is
[HomComplex/TwoLayer.lean](../../Algebra/Homology/ModuleCat/HomComplex/TwoLayer.lean).
The inputs are the existing
[projective-dimension bound](FiniteProjectiveDimension.lean) and
[finite minimal resolution](../../Algebra/Category/ModuleCat/MinimalFiniteFreeResolution.lean).
