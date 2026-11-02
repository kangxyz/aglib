# Strict decrease of the actual singular-height multiset

API: [exists_pointBlowup_heightMultiset_lt](HeightMultiset.lean#L33).

## Inputs and derived outputs

On an actual proper birational normal model over a Nagata rational local
surface, the original singular points have genuine empty levels of their
existing prefixes. The proof of finiteness of the actual old singular set is
an index for its existing multiset, not a chosen finite subset or arbitrary
weight family. The global geometric consumer derives this finiteness proof.

Blowing up an actual singular centre produces genuine empty levels on the new
source and a strictly smaller native height multiset. New singular-set
finiteness is derived from `FinitePrefixGeometry` at the literal zero prefix,
including when there is no singular child. No new-source finiteness,
inequality, future cone, canonical frame or completeness is assumed.

## Actual partition and multiplicities

The original blowdown partitions the new singular points into the actual fibre
of the centre and its complement. Native range and injectivity away from the
centre, together with the original stalk-map isomorphism, identify the latter
with the old singular set minus the centre. Their existing heights agree by
`PointHeight`; every actual fibre height is strictly smaller.

Native Finset identities and Multiset maps give `common + children` for the
new measure and `common + {centre height}` for the old. The removed singleton
is nonempty, so the native Dershowitz–Manna constructor applies. Multiplicities
of equal heights are retained throughout. Local total weight abbreviations
are only proof notation for the existing heights at singular points.

## Boundary

`FiniteResolution` applies this decrease through the native well-founded
relation, preserves every original regular open, and proves normal stages
at the actual chain constructors. Its initial-cone theorem obtains the empty
levels from `FiniteHeight` under the explicit earlier-complete-base input.

The coefficient base is a commutative Noetherian Nagata local domain
of dimension two with `NormalModificationH1Vanishing`. The original
integral normal model is proper, dominant and birational via its original
function-field map. Finiteness of its old singular set and empty-level
witnesses at each singular point are explicit inputs to
`exists_pointBlowup_heightMultiset_lt`; new-source finiteness and
empty levels are conclusions.

Present consumers: [FiniteResolution](FiniteResolution.md).
