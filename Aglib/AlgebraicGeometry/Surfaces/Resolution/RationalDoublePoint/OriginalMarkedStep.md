# Marked continuation on the original scheme step

API: [exists_marked_continuation](OriginalMarkedStep.lean#L33).

The input is an arbitrary original blowup datum at a closed scheme point,
a closed child over that point, and a full parent marker on the original
parent stalk. The parent stalk is a Noetherian local domain. The child is
singular and has genuine normalized maximal-ideal generators, cotangent
finrank three, and the entire normalized square kernel on its original
scheme stalk. No marker on a replacement ring is supplied.

The general PointLocalization endpoint produces the actual closed point of
the original parent-stalk blowup and its native stalk comparison. The exact
forward square identifies the local-blowup stalkScalar with the composite
of that comparison and the original pointLocalRingMap. The child's displayed
generators, cotangent rank and full kernel are transported through that same
native ring equivalence. The existing cotangent-rank helper is exposed once,
without copying its native spanFinrank proof or adding a rank premise on the
local-blowup child.

The existing actual marked-cover theorem then produces a full marker on that
local-blowup stalk. The existing full MarkedCubic.map returns it to the
original scheme stalk. The unique ParameterEquiv transport retains the image
of the same parent parameter, minimality, the original principal centre,
and bijectivity of the original structural residue map. The distinguished
a2 coefficient retains its original residue equation.

This is one genuine continuing original scheme step. It does not construct
the parent marker or child Hilbert geometry, replace the original path by
localizations, identify normalized and ordinary blowups, assume child
completeness, or prove a whole marked tail or finite termination.

Present consumers: [OriginalMarkedPath](OriginalMarkedPath.md).
