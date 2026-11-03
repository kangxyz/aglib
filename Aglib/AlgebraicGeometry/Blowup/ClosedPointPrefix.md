# Original closed-point prefixes

`ClosedPointPrefix.lean` constructs finite selected-point histories using only
the existing native `blowupDatum` at each original scheme point. Each prefix
type lies in `Type u`; one recursive sigma bundle keeps its actual endpoint
scheme and point, without introducing another blowup model. Its computational
scaffolds are exposed only because the public prefix implementation reduces
through them; proof-only helpers remain private.

An arbitrary point predicate controls eligibility. A child is an actual
globally closed eligible point above the previous point. Its closedness and
original blowdown equality are retained. Later singular-point consumers
must derive that closedness from their own geometric hypotheses.

`parent`, `truncate` and their laws retain the original finite history.
`parentFiberEquiv` identifies a one-step fibre with its actual child type.
`child_finite` and `parent_fiber_finite` require an explicit finite eligible
set on the actual blowup source; they do not derive geometric finiteness.

`path` takes a compatible sequence of prefixes, a closed nongeneric root,
and an integral locally Noetherian original scheme. It constructs the
existing `Arc.ClosedPointBlowupPath`. Its Cartier and universal fields come
from the same native blowups after equality elimination. `path_down` exposes
the original datum map followed only by target equality transport, and
`path_transition` identifies the literal original `pointLocalRingMap`.

No arc, future marking, finite height, regular iterate, or termination is
assumed or concluded. This leaf does not invoke König's lemma. Its import of
`Arc.MarkedPath` is for the existing path type and original local-ring maps,
not an arc hypothesis.
