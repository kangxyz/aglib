# Hyperplane powers on the full coefficient curve

[Geometric](Geometric.lean) works on the original closed projective curve
over an algebraically closed field, with the closed-stalk regular-primary
parameter condition. For `L=j*O(1)` it assumes `h0(O)=1`, `H1(O)=0`,
`H0(L^∨)=0` and `h1(L^∨)=1`, and derives `H1(L^r)=0` and
`h0(L^r)=2r+1` for every natural `r`. Its alternative first-power input
uses `h0(L)=3`.

[ScalarExtension](ScalarExtension.lean) transports the original ordinary
cohomology maps through an algebraic algebraically closed field extension.
[BaseChange](BaseChange.lean) gives the resulting ranks over the original
arbitrary field. The original projective pullback, inverse line, tensor
powers and structural scalar actions are retained. The curve and finite
Cartier hyperplane may be nonreduced; no orientation of a coefficient line
or canonical-sheaf base-change theorem is used.
Exceptional Hilbert computations consume these numerical interfaces.

Present consumers include [Conditional resolution from original full quadratic cones](../../../../../../Surfaces/Resolution/RationalDoublePoint/README.md).
