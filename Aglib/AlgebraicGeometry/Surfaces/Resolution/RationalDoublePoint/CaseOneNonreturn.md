# Geometric Case-I fixed-parameter successors

API: [exists_ordinary_stalk_fixed_parameter_successor](CaseOneNonreturn.lean#L46), [exists_ordinary_fixed_parameter_successor_at_singular_point](CaseOneNonreturn.lean#L102).

The pure original-stalk relation, full-kernel/nonreturn consumer and both-
chart coverage are publicly imported from CaseOneNonreturn.Core, with one
implementation of each declaration and unchanged original maps.

`exists_ordinary_stalk_fixed_parameter_successor` derives the child's domain,
normality, Noetherianity, Nagata property, dimension and universal rationality
from the actual rational ordinary-blowup geometry. The genuine relation
constructor supplies three actual maximal-ideal generators before any child
Hilbert input. Nonregular dimension two gives cotangent rank three by the
shared native rank theorem. Ordinary exceptional first-power numerics then
give all graded ranks on that literal stalk, and the existing pure consumer
identifies the entire original quadratic kernel.

Neither inverse-line H0/H1, child Gorensteinness, a canonical frame, a child
Hilbert function nor a child kernel is an input. The parent quadratic
presentation remains genuine data; initial rational Gorenstein recognition
is a separate upstream task.

`exists_ordinary_fixed_parameter_successor_at_singular_point` handles every
actual singular child without a preferred-chart, global-closedness or
base-point premise. Those point properties come from the original rational
ordinary-blowup geometry, and the existing two-chart coverage produces the
actual chart presentation. The successor parameter is exactly the original
structural image of t, with maximal-ideal generation, minimality, the original
centre and residue-map bijection, full nonsquare kernel, fixed-good binary
restriction, and the next genuine Case-I presentation.

The source is the canonical ordinary maximal-ideal blowup of the original
local ring. Transport to an arbitrary original scheme-point blowup uses the
separate native point-localization adapter and actual ring/scalar comparisons.
No degreewise Hilbert transport from an ungraded associated-graded isomorphism,
completed child, finite-over-initial-base child, or path termination is asserted.

The geometric successors assume a commutative normal Noetherian Nagata
local domain `A` of dimension two with
`NormalModificationH1Vanishing A`. The chart version takes a nonzero
parameter and nonzero quadratic affine equation of degree at most two
which is not a nonzero scalar affine-linear square, together with its
presentation and a singular child. The chart-independent version takes
a generating triple, its full nonzero homogeneous quadratic kernel, and a
nonzero nonsquare first-zero binary restriction. Its only point input is
an actual singular point on the ordinary maximal-ideal blowup.

Present consumers: [OriginalCaseOneStep](OriginalCaseOneStep.md).
