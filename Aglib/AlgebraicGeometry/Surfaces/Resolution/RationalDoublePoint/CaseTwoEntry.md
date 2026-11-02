# First entry on the original ordinary-blowup stalk

API: [marker_or_tripleEntry_at_closed_point](CaseTwoEntry.lean#L34).

The parent data consists of its actual normalized maximal-ideal generators,
full normalized canonical quadratic kernel, and a true original cubic with
nonzero original residue polynomial. The child is an actual globally closed
exceptional singular point in the displayed parameter chart. Its normalized
generating triple, cotangent finrank three and full square kernel are honest
inputs on the original scheme stalk.

The theorem itself invokes the original point producer for P/q/Q, local
dimension and singularity, and the native stalk comparison with its exact
stalkScalar square. The shared full target-generator helper derives the
literal primeTriple kernel. Native entry_reduction then supplies either a
full parent MarkedCubic or the entire first TripleEntryData identity.

The latter is transported by the existing full TripleEntryData.map through
the inverse native stalk equivalence, not by transporting its coefficients
alone. Its parameter is the original stalkScalar image of the parent t,
and its coefficient is the original stalkScalar image of the same true
cubic's a3. The unique lower ParameterEquiv transport retains minimality,
the original principal exceptional-centre identity and bijectivity of the
original structural residue map. No desired localized kernel or transported
entry identity is supplied as a premise.

This is one parameter-chart first-entry theorem. It does not cover both
initial charts, perform the subsequent triple-entry step, replace the
original scheme path by a localization path, supply child geometry, or
establish a marked tail or finite termination.

The parent coefficient ring is a commutative Noetherian local domain.
The displayed child generators and full kernels are on the original child
stalk and use its original residue field.

Present consumers: [CaseTwoEntryCover](CaseTwoEntryCover.md).
