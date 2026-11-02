# Normalized-point domination over an affine Nagata base

Source: [AffineBase.lean](AffineBase.lean).

Import `Aglib.AlgebraicGeometry.Surfaces.Birational.NormalizedPointDomination.AffineBase`.

`exists_domination_of_nagata_base` starts with a commutative integrally closed
domain `A`, `IsNagataRing.{u,0} A`, and `ringKrullDim A ≤ 2`.
The supplied map `q : Y ⟶ Spec A` has integral source, is proper and dominant,
and has invertible original `functionFieldMap q`. Normality or regularity of
`Y` is not a premise.

It constructs `T`, `beta : T ⟶ Spec A`, `a : T ⟶ Y` and a literal finite
`NormalizedPointBlowupChain beta`, with `a ≫ q = beta`.
The terminal `T` is integral, normal, Noetherian and of dimension at most two.
Both arrows are proper and dominant and have invertible original
function-field maps. Regularity of `T` is not concluded.

`AffineBaseCharts` supplies Nagata for the original affine charts of `Spec A`;
the general domination theorem then constructs the chain. Its finite DVR-order
and contracted-curve-count inductions are performed internally.
The rational-domination consumer additionally starts with a regular model;
completion rationality uses the constructed chain without requiring its
terminal to be regular.

Present consumers: [Ideal](Ideal.md), [RationalSingularities/Completion](../../RationalSingularities/Completion.md), [Resolution/RationalDomination](../../Resolution/RationalDomination.md).
