# Projective twist coefficient comparisons

[Coefficients.lean](Coefficients.lean) reexports the canonical
[bounded model](Coefficients/Model.md) and the original
[unit and section equations](Coefficients/Sections.md). The model, coefficient
tensor maps, installed derived comparison and section isomorphisms each have
one implementation in those providers.

The entry retains three original coefficient-naturality theorems:

- `twistingFiniteCechTensorCoefficientsIso_naturality` compares the finite
  tensor model along an arbitrary homomorphism of coefficient modules.
- `twistingFiniteCechTensorBottomMap_naturality` retains the actual bottom
  homology inclusion and the native single-complex tensor comparison.
- `twistingDerivedGlobalSectionsTensorCoefficientsIso_naturality` compares
  the same installed derived global sections in the sharp range `-(n : ℤ) ≤ d`.

The common geometric universe, commutative base ring, finite coordinate type
and dimension equivalence `ι ≃ Fin (n + 1)` are unchanged. The first two
naturality statements do not require the sharp degree bound. No Noetherianity
or coefficient-flatness assumption is added. The original constructors,
public names, coefficient morphisms and three naturality proofs are retained.
