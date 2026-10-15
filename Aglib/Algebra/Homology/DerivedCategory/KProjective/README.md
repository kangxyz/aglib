# Actual representatives from native K-projective complexes

Import `Aglib.Algebra.Homology.DerivedCategory.KProjective.Representative`.
In `CochainComplex.IsKProjective`, `Q_map_surjective P L` represents every
actual morphism `Q(P) → Q(L)` by an actual chain map `P → L` with the literal
same `Q.map` value. The source has Mathlib's native `IsKProjective` property;
no projectivity or boundedness is required of the target. Category-object,
morphism and installed derived-category universes remain independent.

`exists_quasiIso_of_derivedIso P L e` retains the displayed actual derived
isomorphism: its constructed chain representative is a quasi-isomorphism
and its `Q.map` is exactly `e.hom`. The proof uses native
`Qh_map_bijective`, fullness of the original homotopy quotient, the original
quotient/localization comparison, and native reflection of isomorphisms
under `Q`. It does not infer a derived-object isomorphism from homology.

The current consumer turns the canonical projective-model Cech/resolution
zigzag into a real map to the original injective-resolution section complex.
This keeps its original derived normalization before native exact tilde and
the original affine adjunction counit are used for a direct-image model.

The leaf passed alone with receipt `1792104059529814000-57132` through the
shared guarded wrapper, with no whole-library compilation.
The external `KProjectiveRepresentativeConsumer.lean` passed with receipt
`1792104303153110000-62123`, checking independent object, morphism and
derived-category universes. Both public declarations use only `propext`,
`Classical.choice` and `Quot.sound`.
