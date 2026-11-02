# Actual closed singular centres

API: [finite_closed_singularSet_of_finiteType_complete_local](ClosedSingularPoints.lean#L30).

Normality and Noetherianity of an actual stalk of dimension at most one
make it either a field or a discrete valuation ring, hence regular.
The existing coheight bound for a nonclosed scheme point on a surface
therefore proves that every singular point is closed. The same regularity
argument and the global dimension bound force its stalk dimension to be
two. There is no separatedness, Jacobson, coefficient-field or resolution
assumption in these pointwise statements.

The final complete-base theorem combines these actual point statements
with [FiniteSingularLocus](FiniteSingularLocus.md). The original singular
set is finite and closed, and each member is a closed point with an actual
two-dimensional stalk. Thus its elements are eligible centres for the
existing point-blowup chain constructor.

Normality and dimension of the actual model remain explicit geometric
hypotheses. For an ordinary rational blowup, use its genuine normality
and dimension producers. This supplies finite branching data, not a
marker, decreasing measure, finite-height result or resolving chain.

The four general pointwise declarations are owned by
[Surfaces/NormalPoints](../../NormalPoints.md) and publicly re-exported here.
The complete-base theorem assumes a commutative complete Noetherian local
ring `A` with `ringKrullDim A ≤ 2`, integral Noetherian `X`, a locally
finite-type `f : X ⟶ Spec A`, `NormalStalks X` and
`topologicalKrullDim X ≤ 2`.

Present consumers: [RationalSingularities/RegularTarget](../../RationalSingularities/RegularTarget.md), [Resolution/CompletedIntermediateBranch](../CompletedIntermediateBranch.md), [Resolution/QuasiExcellentConditions](../QuasiExcellentConditions.md), [BlowupSingularPoints](BlowupSingularPoints.md).
