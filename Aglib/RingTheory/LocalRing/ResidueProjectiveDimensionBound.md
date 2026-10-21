# Finite projective dimension over Noetherian local rings

[ResidueProjectiveDimensionBound.lean](ResidueProjectiveDimensionBound.lean)
develops the upper bound required by
[Stacks Lemma 10.110.4, tag 00OB](https://stacks.math.columbia.edu/tag/00OB).

`ModuleCat.projectiveDimension_le_ringKrullDim_of_finite` concerns the actual
value `projectiveDimension M`.
The supplied natural number `n` only witnesses finite projective dimension;
the assertion does not bound every such `n` by the ring dimension. The actual
residue-field specialization is
`ModuleCat.residueField_projectiveDimension_le_ringKrullDim`.

The proof first shows that reduction modulo an element regular on both the
ring and module preserves finite projective-dimension bounds over the
principal quotient. It then inducts on a finite upper bound for the ring's
Krull dimension. A regular element reduces that bound for the quotient;
dimension shifting and the existing regular-quotient restriction theorem
recover the required bound for the original module. If no regular element
lies in the maximal ideal, a nonzero socle element and a minimal finite free
cover force every finite module of finite projective dimension to be
projective.

The result applies to every finite module of finite projective dimension over
a commutative Noetherian local ring. The residue-field assertion is a
specialization. Regularity of the ring, a dimension bound on the supplied `n`,
and an Auslander–Buchsbaum or Buchsbaum–Eisenbud theorem are not premises.

The minimal-cover supplier is
`ModuleCat.exists_minimal_finite_free_cover` in
[MinimalFiniteFreeResolution.lean](../../Algebra/Category/ModuleCat/MinimalFiniteFreeResolution.lean).
The quotient restriction input is
[QuotientProjectiveDimension.lean](../Regular/QuotientProjectiveDimension.lean).
The implementation uses the pinned Mathlib revision
`d13f23b723b8a846827a245b89c10fc7d3f11612` and Lean 4.34.1.
