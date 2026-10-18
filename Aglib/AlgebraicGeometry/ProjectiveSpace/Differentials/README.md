# Actual projective differentials and Euler arrows

[Euler](Euler.lean) preserves the public import for the actual polynomial
`ProjectiveSpace R ι` and its original structure morphism `toSpec R ι`.
[Basic](Euler/Basic.lean) owns the global objects, augmentation, ratios, and
kernel vectors; [PolynomialChart](Euler/PolynomialChart.lean) owns the actual
differential chart frame; [MiddleFrame](Euler/MiddleFrame.lean) owns the
original tensor middle frame; and [LocalExact](Euler/LocalExact.lean) owns
the actual chart arrows and their explicit short-exact splitting.

The coefficient module
`eulerDegreeOneModule` is the actual `MvPolynomial.homogeneousSubmodule ι R 1`.
Its original coordinate basis induces `eulerCoefficientIsoFree` on the actual
pullback of its tilde sheaf. The Euler middle object retains the orientation
`O(-1) ⊗ π*V`, with this original degree-one module `V`.

`eulerEvaluation` sends the pulled-back coordinate generators to their original
homogeneous sections of `O(1)`. `eulerAugmentation` composes its tensor with the
original twist multiplication and zero-twist identification with the original
unit. On every coordinate subopen it sends `(1/X_i) ⊗ e_j` to `X_j/X_i`.
This actual augmentation is an epimorphism, by the explicit local preimage
`(1/X_i) ⊗ e_i` of one. No field, Noetherian, nontrivial, finite-coordinate,
or exactness-family premise is used for these arrows and equations.

The original sections `eulerKernelGenerator` are
`(1/X_i) ⊗ e_j - (X_j/X_i) ((1/X_i) ⊗ e_i)`, and their image under the actual
augmentation is proved zero. The coordinate formula follows
[Stacks Project Lemma 50.11.1](https://stacks.math.columbia.edu/tag/0FMG),
whose verification of exactness is omitted in that source.

`eulerCoordinateRatio_eq_fraction` identifies those same coordinate coefficients
with the original homogeneous-localization fractions. `eulerPolynomialChart`
uses the original coordinate-open polynomial isomorphism, and its composite
with the structure map is the native spectrum map of `MvPolynomial.C`.
`eulerPolynomialOmegaFrame` supplies a free frame of the actual relative
differential sheaf on that native chart, indexed by the other coordinates.
The accompanying `eulerPolynomialOmegaFreeIso_hom_d` retains the original
relative `d` on every principal open, through the literal `ΓSpecIso.inv`,
restriction, and original chart section isomorphism. The native polynomial
basis and its `D(X_j)` equation are transported together through the native
algebra-map equality; no differential object or map is replaced.

`eulerInverseTwistOnPolynomialChartIso` retains the original inverse-coordinate
frame through the original chart structure-sheaf isomorphism.
`eulerMiddlePolynomialFreeIso` then frames the actual restricted tensor middle
object on that same native polynomial chart. Its generator formula sends each
original `(1/X_i) ⊗ e_j` to the corresponding original free section. The
construction uses the native tensor restriction, original left unitor, and
native free-sheaf restriction isomorphism; it also supports arbitrary `ι`.

`eulerKernelSectionOnPolynomialChart` retains the original compatible
kernel-vector sections. `eulerDifferentialOnPolynomialChart` is a constructed
arrow from the actual restricted relative differential sheaf to the actual
restricted Euler middle sheaf. Its original relative-`d` formula on every
principal polynomial-chart open is proved, and its composite with
`eulerAugmentationOnPolynomialChart` is zero. The latter arrow is exactly the
restriction of the original augmentation followed by the original unit
restriction isomorphism.

`eulerPolynomialChart_polynomialToSection` matches the original whole chart
section maps. `eulerCoordinateRatio_eq_polynomialSection` identifies the
original homogeneous ratio with the original inverse-chart image of its
native polynomial coordinate on every chart open.
`eulerDifferentialOnPolynomialChart_d_ratio` therefore states the original
Euler formula directly: the actual relative `d(X_j/X_i)` maps to the original
kernel vector displayed above, on every principal polynomial-chart open.

`eulerShortComplexOnPolynomialChart_shortExact` proves the actual relative
Euler sequence short exact on every original polynomial chart. Its explicit
splitting uses the complementary-coordinate projection and the original
distinguished-coordinate vector. The left inverse, right inverse, and middle
decomposition equations are proved as native sheaf-map equalities. This
includes the one-coordinate case with an empty complementary basis, and uses
no finiteness, field, Noetherian, nontriviality, or exactness-family premise.

[Overlap](Euler/Overlap.lean), imported separately as
`Aglib.AlgebraicGeometry.ProjectiveSpace.Differentials.Euler.Overlap`, proves
transition identities for the original ratios, inverse-twist and middle
generators, relative differentials and kernel vectors. The latter two obey
the same quotient-rule formula in the original transition unit.
`eulerDifferentialOnPolynomialChart_d_ratio_open` extends the original
differential/kernel-vector equation to every polynomial-chart open. These
results retain arbitrary coordinate types and commutative base rings.
The `Euler` entry reexports `LocalExact`; it does not import `Overlap`.

Equality and gluing of the chart arrows, and the global short exact Euler
sequence, remain separate obligations. No determinant, canonical bundle,
trace, or residue identification is asserted by these results.
