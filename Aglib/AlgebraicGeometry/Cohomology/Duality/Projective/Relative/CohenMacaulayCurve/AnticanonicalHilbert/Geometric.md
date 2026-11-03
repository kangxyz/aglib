# Genuine regular-hyperplane Hilbert numerics

`cmCurve_hyperplanePower_cohomology_of_isAlgClosed` works on the full actual
closed projective curve over an algebraically closed field, under the native
closed-stalk CM-parameter condition. For the pulled-back line `L=j*O(1)`, it
uses honest `h0(O)=1`, `H1(O)=0`, `H0(L∨)=0`, and `h1(L∨)=1` to conclude
`H1(L^r)=0` and `h0(L^r)=2r+1` for every natural r.

The structure-sheaf H0 hypothesis first proves nonemptiness. A genuine closed
point is rational over the algebraically closed field. The existing regular
hyperplane-through-that-point theorem produces an actual finite Cartier
zero scheme; it does not require a circular three-section bound. Its ideal
is identified with the original inverse line by the existing zero-ideal
isomorphism. The same hyperplane's dual-ideal isomorphism and the original
Cartier numerical theorem compute all powers. The full curve and divisor,
including their nilpotents, are retained.

This is a distinct algebraically closed geometric stage. The arbitrary-field
consumer in `BaseChange` uses ordinary cohomology and line-power scalar
extension to descend its H0 dimensions. No canonical-module gluing or
canonical-generation result is part of either numerical argument. The actual
canonical origin of the inverse-line cohomology is an upstream obligation.

## First-power input, without inverse-line cohomology

`cmCurve_hyperplanePower_cohomology_of_firstPower_of_isAlgClosed` keeps the
same actual closed projective curve and closed-stalk CM-parameter condition.
Its numerical inputs are only `h0(O)=1`, `H1(O)=0`, and `h0(L)=3` for the
original positive line `L=j*O(1)`. It concludes the same all-power H0 formula
and H1 vanishing, without inverse-line or canonical hypotheses.

The genuine regular finite hyperplane and its original dual-ideal isomorphism
supply the finite Cartier input. The first-power numerical producer computes
divisor H0 dimension two; both geometric endpoints then use the single
finite-Cartier induction. No divisor over an arbitrary original field is
assumed by this algebraically closed stage.
