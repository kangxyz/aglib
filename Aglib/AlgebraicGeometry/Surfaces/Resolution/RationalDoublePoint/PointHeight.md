# Actual point-blowup singular-height step

API: [pointBlowup_singularHeight_step](PointHeight.lean#L88).

The source is the original proper birational normal model of a Nagata rational
local surface. At each original singular point there is a genuine empty level
of its existing singular prefixes; the final initial-cone consumer derives
these witnesses rather than assuming a termination certificate.

The actual blowup at a selected singular point inherits those empty levels.
Over the centre, actual closed singular points are literal children, so the
existing reroot theorem gives strict decrease of the existing least height.
Away from the centre, two original open maps from the same complement pullback
identify the original prefix levels and their least empty indices. The native
blowdown stalk-map isomorphism supplies actual singularity correspondence.

All geometric facts needed on the new source are derived: actual integral,
proper, dominant and birational map; normality of every stalk from the unique
PointNormality theorem; and global closedness of singular points from the
original rational-model theorem. No child completeness, later cone, Hilbert
row, canonical frame or Gorenstein premise is introduced.

`HeightMultiset` uses these pointwise comparisons and the original
complement isomorphism to prove the strict multiset inequality.
`FiniteResolution` then preserves every original regular open and proves
normal stages before the explicit normalized-terminal comparison.

The base is a commutative Noetherian Nagata local domain of dimension two
with `NormalModificationH1Vanishing`. The original model is integral and
normal, with proper dominant structural map and invertible original
function-field map. The selected centre is singular, and empty levels at
every original singular point remain the inputs to
`pointBlowup_singularHeight_step`.

Present consumers: [HeightMultiset](HeightMultiset.md).
