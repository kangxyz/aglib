# Finite singular branching of the actual rational blowup

API: [finite_closed_singularSet_of_complete](BlowupSingularPoints.lean#L32).

The input is a complete Noetherian normal local domain A of dimension two,
with genuine universal `NormalModificationH1Vanishing A`. The scheme is
exactly the existing ordinary maximal-ideal blowup `source A hd` and the
morphism is exactly its original `map A hd`.

Completeness gives Nagata of A. The existing `ordinary_normalStalks` and
`ordinary_dimension_le_two` derive the actual model hypotheses from that
Nagata property and rationality. Properness of the original blowdown gives
quasi-compactness; its existing locally Noetherian instance makes the model
Noetherian. The complete-base finite-singular theorem then supplies a finite
closed singular set, with every member closed and having a two-dimensional
actual stalk.

No Gorensteinness, quadratic chart, ADE classification, marking, resolving
model or termination measure is required for this finite-branching result.
It applies to regular rational input rings as well. It does not prove
rationality or Gorensteinness of child stalks and does not prove finite
height of an iterated singular-descendant tree. Later noncomplete children
must remain on their original finite-type models over the original complete
base; this theorem does not assert that their local rings are complete.

Present consumers: [BlowupChildren](BlowupChildren.md).
