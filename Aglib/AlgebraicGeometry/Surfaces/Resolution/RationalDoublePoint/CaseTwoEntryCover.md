# First entry on both original exceptional charts

API: [marker_or_tripleEntry_at_closed_point](CaseTwoEntryCover.lean#L55).

The same true original cubic F is used on the entire original two-chart
cover. The opposite chart uses precisely CubicRelation.swap. Its reduced
polynomial is nonzero because the existing four coefficient laws reverse
the original four coefficients; no new cubic, field extension or polynomial
classification is constructed.

The existing original two-chart coverage and parameter-chart Entry theorem
now produce either a full parent marker, or a full TripleEntryData on the
original child stalk. The output records exactly one of the two original
possibilities: its parameter and coefficient are the original stalkScalar
images of t and F.a3, or of s and F.a0. Original minimality, exceptional-centre
identity and bijectivity of the original structural residue map are retained.
There is no preferred-chart, transported-entry or supplied primeTriple-kernel
premise. Actual child generators, rank and full kernel remain honest inputs.

This proves only the first entry on the actual cover. The next triple-entry
step, actual original-path comparison, construction of marked tails and
finite termination remain separate. In particular it does not assert the
rejected special-cubic preservation statement.

The parent coefficient ring is a commutative Noetherian local domain.
The displayed child generators and full kernels are on the original child
stalk and use its original residue field.

Present consumers: [OriginalEntryStep](OriginalEntryStep.md).
