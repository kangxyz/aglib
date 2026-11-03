# Canonical homology and native self-injective dimension

[CanonicalModule](CanonicalModule.lean) uses a finite ring map `R → S`,
regular local `R` of specified finite dimension, Noetherian local `S`
and ambient Ext concentration in degree `n`.
The coefficient `K` is the same degree-`n` homology of installed derived
coinduction of `R`. A native finite self-injective-dimension bound for `S`
constructs an `S`-linear frame `K ≃ S`.
The frame is chosen, with no preferred normalization.

[NormalQuotient](NormalQuotient.lean) starts with a surjective local
`P → S`, regular local `P`, normal Noetherian local domain `S`,
`dim S=r≤2` and `dim P=n+r`.
It derives ambient Ext concentration and injective dimension at most `r`
for that actual coinduced canonical homology.
A regular-sequence kernel is not an input.

[NormalQuotientCanonical](NormalQuotientCanonical.lean) combines these
interfaces to identify finite native self-injective dimension of `S`
with existence of a linear frame of the same `K`. Actual ambient
coefficient-line frames are transported through the original coinduction
and homology maps. The normal-surface stalk application retains the
original quotient map, dimensions and scalar action.

Present consumers include [Canonical coefficients on embedded normal surfaces](../../AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/README.md), [Original canonical trace and local evaluation](../../AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/Trace/README.md).
