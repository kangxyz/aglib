# Rationality propagation to actual stalks

Source: [RationalPropagation.lean](RationalPropagation.lean).

`normalModificationH1Vanishing_stalk_of_normalModificationH1Vanishing`
starts with a two-dimensional Nagata Noetherian local domain A with universal
normal-modification structure-H1 vanishing. For every actual integral normal
proper dominant model X with its original function-field map an isomorphism,
each closed nongeneric stalk of X has the same universal vanishing property.
Neither A nor the stalk must be complete. There is no chosen resolution or
Gorenstein hypothesis, and Nagata is not silently inferred from rationality.

The source dimension bound is obtained from the original Nagata chart maps.
The actual closed fibre misses the generic point, so its dimension is at most
one. Local formal functions and injectivity into completion imply original
H2(X,O) vanishing without completeness. For any further normal modification
Y→X, its composite over A has H1(Y,O)=0 by the original rationality premise.
The original Leray edge is surjective because H2(X,O)=0. Thus the original
R1 has no global sections; its finite closed support detects that it is zero.
Finally the actual local replacement and its exact Cartesian square
identify the caller's local H1 with the original R1 stalk.

The reusable intermediate `original_R1_isZero_of_structureH1_structureH2`
records this original Leray argument for any normal Noetherian integral
surface with the two actual cohomology vanishings. Its hypotheses are not
substituted for the conclusion in the rationality theorem: they are derived.
The private finite-support and Nagata-dimension implementations in the owning
R1 module were exposed by the root integrator, without duplicating proofs.

This is a propagation theorem, not construction
of a rational model, completion-rationality, or rational Gorenstein reduction.

Direct consumers: [AlgebraicGeometry/Surfaces/RationalSingularities/ModelLocalization](../ModelLocalization.md), [AlgebraicGeometry/Surfaces/RationalSingularities/RegularTarget](../RegularTarget.md), [AlgebraicGeometry/Surfaces/Resolution/RationalDoublePoint/BlowupChildren](../../Resolution/RationalDoublePoint/BlowupChildren.md).
