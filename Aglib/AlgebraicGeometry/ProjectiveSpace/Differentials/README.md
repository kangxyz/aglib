# Actual projective differentials and Euler arrows

[Euler](Euler.lean) uses the actual polynomial `ProjectiveSpace R ι` and its
original structure morphism `toSpec R ι`. The coefficient module
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

`eulerKernelSectionOnPolynomialChart` retains the original compatible
kernel-vector sections. `eulerDifferentialOnPolynomialChart` is a constructed
arrow from the actual restricted relative differential sheaf to the actual
restricted Euler middle sheaf. Its original relative-`d` formula on every
principal polynomial-chart open is proved, and its composite with
`eulerAugmentationOnPolynomialChart` is zero. The latter arrow is exactly the
restriction of the original augmentation followed by the original unit
restriction isomorphism.

Local injectivity, generation of the whole kernel, compatibility and gluing
of the chart arrows, and the global short exact Euler sequence remain the
next obligations. No determinant, canonical
bundle, trace, or residue identification is asserted by this checkpoint.
