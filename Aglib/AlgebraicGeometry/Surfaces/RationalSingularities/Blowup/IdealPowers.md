# Original ideal powers on the normalized rational surface blowup

This module proves the ideal-power section argument on the literal normalized
ordinary maximal-ideal blowup constructed in [Blowup](../Blowup.lean).
The original local ring A is a commutative Noetherian Nagata domain of dimension
two, with the existing `NormalModificationH1Vanishing A` predicate. Normality
of A is used for the original global coefficient bijection and the resulting
section-image induction.

`normalizedIdealSection` pulls each actual maximal-ideal element through the
original ordinary blowup row and normalization ideal-pullback isomorphism.
Its inclusion is `unitMul` by the image of that same element under the original
structural map `coefficients A hd`. The initial affine epimorphic row is derived
from the span of the actual ideal generators, using the original tilde module
and its native finite-free comparison. Noetherianity supplies such a finite
row for the full maximal ideal.
The finite generator index is canonically lifted to the scheme universe;
each lifted index evaluates to the same original ideal element.

Finite rows are preserved under the original pullback, quotient and tensor
maps. Induction constructs finite rows for every actual tensor power. The
native Cartier power comparison identifies these with the original ideal-power
modules, so `normalizedIdealPower_H1` proves H1 vanishing in all nonnegative
degrees. The coherent-row theorem in the lower module derives the needed
kernel coherence and H2 vanishing.

For the original row with kernel F, the existing ordered cross-relation map
constructs a finite row onto F tensor I. Tensoring these sections with the
previous actual power gives finite rows for every positive kernel twist.
`normalizedIdealKernelPower_H1` derives their H1 vanishing. The resulting
`normalizedIdealTensorRow_global_surjective` and
`normalizedTensorPowerRow_global_surjective` retain the actual tensor and
finite-coproduct presentations of the original row. The decomposition theorem
expresses each next-power section as a finite sum using those same components.

The section-image statements keep the original structural coefficient map
alpha from A to Gamma(Y,O_Y). For the original closed ideal J on Y, define

```
K_n = (ker(Gamma(Y,O_Y) -> Gamma(V(J^n),O))).comap(alpha).
```

The native `idealSectionsEquiv` identifies this kernel with the image of the
original inclusion Gamma(J^n) -> Gamma(O_Y). The displayed `J` is exactly
`normalizedExceptionalIdeal`, and `normalizedPowerSectionIdeal_eq_original`
retains this literal ideal rather than only its kernel presentation.

In degree one, the original generator sections show m is contained in K_1.
The actual exceptional support is nonempty, so K_1 is proper; maximality gives
K_1 = m. In positive degrees, the original global row surjectivity gives
K_(n+2) = m * K_(n+1). Both directions use the original Cartier product,
coefficient map and row components. The zeroth ideal is the whole ring.
Thus `normalizedIdealPower_sectionImage` proves K_n = m^n for every n.
Together with the proved bijectivity of alpha, this is exactly

```
range(Gamma(J^n) -> Gamma(O_Y)) = alpha '' (m^n : Set A).
```

The proof uses the original A-action. It introduces no coefficient-field
section, completion, Gorenstein condition, chosen resolution or presentation
of the desired section algebra. Finite generating rows and positive kernel
H1 are conclusions of the construction.

The mathematical source is [Stacks 54.9.3, 0B4Y](https://stacks.math.columbia.edu/tag/0B4Y),
using the finite cross-relation construction of
[Stacks 27.13.9, 0B3B](https://stacks.math.columbia.edu/tag/0B3B).

[Normality](Normality.md) matches the ordinary-blowup embedding with its
tautological line and applies Serre H1 vanishing, coherent cokernel
generation and the original finite projection formula to descend normality.
The exceptional-fibre quotient sections and H1 vanishing are proved in
[Exceptional](Exceptional.md) and [Powers](Exceptional/Powers.md) using
the original ideal-product and quotient sequences. Those conclusions
are outside this ideal-power module.
