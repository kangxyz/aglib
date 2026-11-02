# Normal stages and normalized presentation of ordinary chains

[ClosedPrefix](ClosedPrefix.lean) realizes the original finite prefix as
a native ordinary point-blowup chain when its root is closed and the
actual truncation centres have dimension-two local rings.

[NormalStages](NormalStages.lean) is a recursive property of the existing
ordinary chain, requiring normality of the actual post-blowup stages.
It composes through the original concatenation; it does not assert
normality of arbitrary point blowups or require normality of the initial
base.

[NormalizedPresentation](NormalizedPresentation.lean) takes an ordinary
chain over an integral base and its proved normal stages. It constructs
a literal normalized-point chain of the same length with an explicit
terminal isomorphism `E` and `E.hom ≫ normalizedMap = ordinaryMap`.
No Noetherian, properness, Nagata or regular-terminal input is added.
The conditional initial-cone resolution endpoint uses this exact triangle.

Present consumers include [Conditional resolution from original full quadratic cones](../RationalDoublePoint/README.md).
