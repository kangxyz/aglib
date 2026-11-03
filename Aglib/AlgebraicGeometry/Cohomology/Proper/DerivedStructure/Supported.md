# Original R1 of a supported local modification

Source: [Supported.lean](Supported.lean).

`firstHigherImage_isZero_of_localStructureH1_of_isIso_complement` retains an
actual quasi-compact quasi-separated f:Y→X, a closed point x, the actual square
`IsPullback a p f (X.fromSpecStalk x)`, and the original restriction isomorphism
off x. Vanishing of the SAME structure H1 on T implies vanishing of the
original R1 of f. No properness, integrality, normality, Noetherianity or
dimension is needed for this intermediate supported-R1 theorem.

The centre uses the existing `originalStructureH1StalkLinearEquiv` with its
original scalar `p.appTop.comp (ΓSpecIso _).inv`. The other stalks use the
existing higher-image vanishing on the actual isomorphism open. The body
is generalized once from the private point-blowup supplier; that old caller
retains its original signature and only assembles its same square/complement.
No new cohomology comparison or support implementation is introduced.

The owner is beside the existing proper-derived surface theorem, rather
than importing that surface closure into a lower module-stalk owner merely
for convenience. The rational-stalk consumer is strictly downstream.

Direct consumers: [AlgebraicGeometry/Surfaces/RationalSingularities/Blowup/DerivedUnit](../../../Surfaces/RationalSingularities/Blowup/DerivedUnit.md), [AlgebraicGeometry/Surfaces/RationalSingularities/DerivedUnit/Supported](../../../Surfaces/RationalSingularities/DerivedUnit/Supported.md).
