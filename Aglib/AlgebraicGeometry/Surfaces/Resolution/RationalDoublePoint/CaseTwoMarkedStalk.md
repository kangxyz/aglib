# A continuing marker on the original ordinary-blowup stalk

API: [cotangent_finrank_ringEquiv](CaseTwoMarkedStalk.lean#L52), [full_square_kernel_in_target_generators](CaseTwoMarkedStalk.lean#L68), [exists_marked_continuation_at_closed_point](CaseTwoMarkedStalk.lean#L113).

The theorem starts with an actual corrected `MarkedCubic` on the parent and
an actual globally closed exceptional singular point in its parameter chart.
Honest child Case-II data is supplied on the original scheme stalk: its
actual normalized generating triple, actual cotangent finrank three, and
entire original normalized quadratic kernel. These are the outputs required
from genuine child geometry, not a desired primeTriple kernel or an assumed
transported marker.

The theorem itself invokes `CaseTwoPoints` to produce the original P/q/Q,
its dimension and singularity, and the native stalk isomorphism with its
literal `stalkScalar` equality. The existing full ring-equivalence transport
maps the given child kernel and generators. Native ideal span-finrank
invariance and the existing local cotangent-rank theorem transport the rank;
finite generation is derived from the actual triple. Native prime-span and
local-triple generation, followed by the existing whole-kernel basis bridge,
derive the full linear-square kernel on the literal primeTriple.

Only then is the existing `marked_continuation` invoked. Its full marker is
mapped back via the inverse native stalk equivalence. The output is a genuine
`MarkedCubic` on the original stalk and an exact equality identifying its
parameter with the original parent's `stalkScalar` image. Its original
coefficient equality, minimality, principal exceptional-centre identity and
bijectivity of the original structural residue-field map are retained.
The marker's actual other/square generators and true cubic are the ones
produced by the existing full `MarkedCubic.map`, whose value formulas remain
available; no coefficient-only substitute is used.

This is one continuing child in the parameter chart. It does not construct
initial or triple entry, prove the other chart's overlap condition, assemble
an entire marked tail, prove Case-I nonreturn, or establish finite termination.
It adds no child completeness or finite-over-original-base assumption.

The parent coefficient ring is a commutative Noetherian local domain.
The displayed child generators and full kernels are on the original child
stalk and use its original residue field.

Present consumers: [CaseTwoEntry](CaseTwoEntry.md), [CaseTwoMarkedCover](CaseTwoMarkedCover.md), [CaseTwoTripleEntry](CaseTwoTripleEntry.md).
