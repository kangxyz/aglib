# Positive exceptional coefficient-canonical twists

Source: [ExceptionalCurveTwistVanishing.lean](ExceptionalCurveTwistVanishing.lean).

## Statement and geometric suppliers

For a Noetherian normal local domain A of Krull dimension two, with Nagata
and original normal-modification H1 vanishing hypotheses, retain the full
ordinary-blowup exceptional scheme E and its original ideal powers.
Given an actual closed immersion j:E→P^m_(A/m), m≥1, its original structural
triangle, and an actual comparison j*O(1)≅I|E, every positive power q satisfies
H1(E,I^q|E⊗ω_(E,V))=0 for any specified finite rank-one coefficient V.
The coefficient is not trivialized. Arbitrary residue fields and nonreduced E
are retained. The embedding/O(1) comparison must still be supplied by the caller;
this adapter does not manufacture them or assume the desired vanishing.

## Proof route

Actual coordinate-power generating sections pull back along j and transport
through native tensor-power comparisons. Their free evaluation factors the
all-section evaluation. The height of m^q equals two, so the native quotient
m^q/m·m^q has dimension at least two. The original exceptionalPowerTheta and
original structural coefficient bijection imply I^q|E is not the unit line.
The actual structural H0 map and actual closed-stalk CM parameter theorem
supply the hypotheses of the original coefficient Serre twist vanishing.

## Shared original structural H0 law

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/ExceptionalCoefficientVanishing](ExceptionalCoefficientVanishing.md).
