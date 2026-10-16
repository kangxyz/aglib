# Extension by zero and closed pushforward

[ClosedImmersion](ClosedImmersion.lean) constructs the single actual exchange
`pushforward b ⋙ extensionByZero j ⟶ extensionByZero a ⋙ pushforward f`
on an original Cartesian open square. Its unit formula is the adjoint of
`pushforward b` of the original source extension unit followed by the
inverse original `cartesianOpenBaseChange`.

Its restriction along `j` is invertible for every coefficient. If `f` is a
closed immersion, the same map is invertible globally: inside the open use
the original restriction/stalk isomorphism, and outside use the actual
extension-by-zero and closed-pushforward zero-stalk formulas. The target
zero-stalk lemma needs only source openness and the original square, without
assuming that `j` is open. No coefficient is assumed QC, finite or coherent.
`closedPushforwardExtensionByZeroIso_hom` is the literal original map.

The native closed-right-adjoint restriction comparison consumes this left
adjoint exchange, preserving the original units and counits. No interchange
of arbitrary internal Hom with stalks is assumed.
