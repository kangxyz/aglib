# Base change for the original normalization

This family compares Mathlib's actual relative normalization and its canonical
base-change map. It retains both structural and original-source projections.

- [AffineLocalization](AffineLocalization.md) proves the comparison for an
  actual localization of affine coefficient rings.
- [Composition](Composition.md) gives the original comparison's composition
  equation and its invertibility consequences.
- [Stalk](Stalk.md) applies the localization theorem to actual local spectra.
- [FlatPreimmersion](FlatPreimmersion.md) derives invertibility for a flat
  preimmersion, using the actual stalk maps and local-spectrum detection.

The results keep their quasi-compact/quasi-separated hypotheses. They do not
assert that arbitrary flat base change preserves normality. The
[function-field specialization](../FunctionField/FlatPreimmersion.md) keeps the
original function-field homomorphism. Local modification descent consumes
these comparisons from this normalization owner.

These results apply to a qcqs original morphism. The affine theorem uses
localization for the algebra of the actual section map; the general
preimmersion theorem retains both flatness and preimmersion.
The [generic normalization comparison](../FunctionField/FlatPreimmersion.lean)
and prescribed local-point-step globalization consume the same native
comparison and its two projection equations. No arbitrary-flat
normalization base-change assertion is made.
