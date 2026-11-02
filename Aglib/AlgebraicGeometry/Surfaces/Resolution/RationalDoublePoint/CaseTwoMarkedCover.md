# Actual coverage of a continuing Case-II marker

API: [mem_parameterChart_of_closed_caseTwo_point](CaseTwoMarkedCover.lean#L34), [exists_marked_continuation_at_closed_point](CaseTwoMarkedCover.lean#L99).

The parent is an actual corrected `MarkedCubic` and the child is an actual
globally closed exceptional singular point of the original ordinary blowup.
The child's normalized generating triple, cotangent finrank three, and full
normalized square kernel are honest inputs on its original scheme stalk.
No preferred-chart, overlap, transported-marker, or primeTriple-kernel
hypothesis is supplied.

`CaseTwoPoints` first gives the actual two-chart cover. In the opposite chart,
the original swapped cubic and native coordinate permutation give the same
literal reduced chart. The original point producer supplies P/q/Q, actual
local dimension and singularity, and the native stalk isomorphism. The
single shared target-generator helper derives the primeTriple's full square
kernel from the genuine original-stalk data. The existing
`marked_opposite_parameter_not_mem` then proves that the original ratio is
outside P. Native localization range and the same `AffineAtlas.overlap`
put this very point in the parent's marker chart.

The original-stalk continuation theorem then supplies a full corrected
`MarkedCubic` whose parameter is the actual `stalkScalar` image of the parent
parameter, with its original coefficient equality, minimality, principal
exceptional-centre identity and original residue-map bijectivity.

This removes only the preferred-chart hypothesis from one continuing child.
It does not construct initial or triple entry, supply child geometry, prove
Case-I nonreturn, assemble a marked tail, or establish finite termination.

The parent coefficient ring is a commutative Noetherian local domain.
The displayed child generators and full kernels are on the original child
stalk and use its original residue field.

Present consumers: [OriginalMarkedStep](OriginalMarkedStep.md).
