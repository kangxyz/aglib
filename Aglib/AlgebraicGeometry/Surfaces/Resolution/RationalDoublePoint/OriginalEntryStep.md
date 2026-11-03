# First entry on the original scheme step

API: [marker_or_tripleEntry](OriginalEntryStep.lean#L31).

The input is an arbitrary original blowup datum at a closed scheme point and
an actual closed child over it. The original parent stalk is a Noetherian
local domain with genuine normalized generators, the full normalized square
kernel, and one true cubic whose original residue polynomial is nonzero.
The original child stalk is singular and has its own genuine normalized
generators, cotangent finrank three and full normalized square kernel.

The existing PointLocalization theorem supplies the actual local-blowup
point and native original-stalk comparison, including its exact structural
square. The existing generator, cotangent-rank and full-kernel transports
supply the local-blowup child's data. The actual two-chart entry theorem
then gives either a full parent marker or complete TripleEntryData.

The complete entry data is returned through the existing TripleEntryData.map,
not merely through a coefficient substitution. With f equal to the literal
original blowdown pointLocalRingMap, the child alternatives are precisely
p=f(t) with coefficient=f(F.a3), or p=f(s) with coefficient=f(F.a0). The
same ParameterEquiv supplier retains minimality, the original centre ideal,
and bijectivity of the original structural residue-field map.

This is one original first-entry step. It does not construct the input
canonical or Hilbert geometry, perform the subsequent triple-entry step,
assume a transported entry identity or marker, identify normalized and
ordinary blowups, assert child completeness, or prove a marked tail or
finite termination.

Present consumers: [OriginalMixedPath](OriginalMixedPath.md).
