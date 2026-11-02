# The actual local coordinate uses the original ordinary mate

Source: [LocalEvaluation.lean](LocalEvaluation.lean).

`LocalEvaluation.lean` proves the element formula

    mu(s) = pushforwardSections(beta(stalkSections(s)))

for the mu constructed in `Localization.lean`, where beta is the original
ordinary Cartesian base-change mate at the actual local-spectrum square.
The proof uses naturality of the original stalk/pullback-sections comparison,
the proved q=0 square of `DegreeZero.lean`, and the native affine H0 evaluation
at `toRightDerivedZero`. It never cancels ordinary global sections or replaces
the given local ring by a complete/finite base algebra.

Combining this identity with `BaseChange.lean` supplies the ordinary mate and
local-coordinate factors of the local canonical evaluation formula. The final
identification with affine tilde/evaluation expressed through rho's inverse
is supplied by the original affine adjunction transport in `AffineEvaluation.lean`
. No canonical
surjectivity or general proper trace-isomorphism assertion is made.

The inverse-localized-trace evaluation theorem identifies rho inverse with the sections of the actual ordinary base-change mate after the pulled-back inverse trace. This is exactly the input to the original counit in `ordinaryTracePullback_baseChange`. The hypothesis is invertibility of the actual trace; properness alone is not used to manufacture it.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/Trace/AffineEvaluation](AffineEvaluation.md).
