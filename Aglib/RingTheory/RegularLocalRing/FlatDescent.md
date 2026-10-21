# Regularity descent along flat local maps

[FlatDescent.lean](FlatDescent.lean) proves the full statement of
[Stacks Lemma 10.110.9, tag 00OF](https://stacks.math.columbia.edu/tag/00OF).

## Interfaces and hypotheses

- `IsRegularLocalRing.of_flat_local` proves regularity of the source of a flat
  local homomorphism from a Noetherian local ring to a regular local ring. The
  source and target universes are independent.
- `ModuleCat.hasProjectiveDimensionLE_of_faithfullyFlat` descends any finite
  projective-dimension bound from `((ModuleCat.extendScalars f).obj M)` to
  the original finite module `M`. The source is Noetherian and `f` is faithfully
  flat. Neither locality nor Noetherianness of the target is required.
- `IsRegularLocalRing.projectiveDimension_le_of_flat_local` bounds the
  projective dimension of every finite source module by the dimension of a
  regular local target. The source is Noetherian local and the displayed
  homomorphism is both flat and local.
- `IsRegularLocalRing.residueField_hasProjectiveDimensionLE_of_flat_local`
  applies that bound to the actual residue field of the source, with bound
  `(IsLocalRing.maximalIdeal S).spanFinrank`.

The homological auxiliary declarations use rings and modules in the same
universe. The final ring theorem uses canonical universe lifts and ring
equivalences. The actual ring homomorphism determines scalar extension and
flatness. There are no finite-type,
unramifiedness, residue-field equality, completion, characteristic or source
regularity assumptions. Target Noetherianness and locality follow from
`IsRegularLocalRing S`.

## Argument and reusable inputs

The faithfully flat projective-dimension theorem is an induction on the bound. At bound
zero the scalar extension is projective, hence flat. Faithfully flat descent
gives flatness of the original module, and its finite presentation gives
projectivity. For the successor step, a finite free presentation has finite
kernel because the source is Noetherian. Flat scalar extension preserves the
short exact sequence and projectivity of the middle term. Dimension shifting
reduces the bound of the extended kernel; induction descends that bound, and a
second dimension shift gives the claimed bound of the original module.

A flat local map is faithfully flat. The existing
`IsRegularLocalRing.projectiveDimension_le_dimension` supplies the bound over
the regular target, so the homological descent theorem descends it.

The regular-target supplier is imported from
[FiniteProjectiveDimension.lean](FiniteProjectiveDimension.lean), selected from
published Aglib revision `53026ed980426d54f2b35b3310e27e2d2cb14293`.
Its regular-quotient input is
[`Regular/QuotientProjectiveDimension.lean`](../Regular/QuotientProjectiveDimension.lean).
The underlying Mathlib revision is
`d13f23b723b8a846827a245b89c10fc7d3f11612`, with Lean 4.34.1.

## Residue-field criterion and scheme consumer

The proved converse
`IsRegularLocalRing.of_residueField_hasProjectiveDimensionLE` in
[ResidueProjectiveDimension.lean](ResidueProjectiveDimension.lean) supplies
[Stacks Proposition 10.110.5, tag 00OC](https://stacks.math.columbia.edu/tag/00OC),
implication (1) to (3). Applying it to the descended residue-field bound proves
regularity of the source. This criterion imports the actual upper bound from
[ResidueProjectiveDimensionBound.lean](../LocalRing/ResidueProjectiveDimensionBound.lean)
and the actual cotangent-space lower bound; it is not an external premise.

[Scheme flat-local descent](../../AlgebraicGeometry/Properties/Regular/Descent/FlatLocal.lean)
now supplies `AlgebraicGeometry.Scheme.RegularityDescent.flatLocalRegularityDescent`,
an inhabitant of the original `FlatLocalRegularityDescent` proposition. The
existing parametric scheme consumers can use this supplied proof directly.
