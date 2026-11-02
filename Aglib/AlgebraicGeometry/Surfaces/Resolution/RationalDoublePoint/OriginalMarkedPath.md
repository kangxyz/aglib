# A marking on the original continuing Case-II path

API: [exists_marking_of_initial_marker](OriginalMarkedPath.lean#L31).

`exists_marking_of_initial_marker` takes the original
`P : Arc.ClosedPointBlowupPath`, an initial
`t0 : maximalIdeal (P.localRing 0)`, a full `M0 : MarkedCubic t0`,
and `t0 ∉ maximalIdeal (P.localRing 0)^2`.

For every original child, the inputs are nonregularity, a normalized
maximal-ideal generating triple, raw quotient-cotangent finrank three,
and the entire normalized square kernel. Future markers, chart membership,
residue bijectivity and exceptional-centre identities are conclusions of
the continuation construction, not additional supplied data.

At the literal `P.datum n` and points, `OriginalMarkedStep` constructs a
full marker on `P.localRing (n+1)`. Dependent recursion retains a parameter
and marker at each stage. The one-step equation and original scalar recursion
prove that the parameter is `(P.scalar n).hom t0`.
These identities, minimality and the derived residue and centre equations
fill the existing `P.Marking`, with initial parameter exactly `t0`.

`OriginalMixedPath` constructs the initial marker and the continuing
Case-II data from its supplied initial full cone and rational path geometry.
In the second-entry branch the ratio parameter is distinguished from the
previous exceptional denominator, and the marking begins at the later tail.

Termination then uses the complete-base marked-tail theorem with the
original composed local injection and finite residue map.
No later stalk completeness or finite-over-base assertion is introduced.

Present consumers: [OriginalMixedPath](OriginalMixedPath.md).
