# Domination by induction on contracted curves

Source: [CardinalityInduction.lean](CardinalityInduction.lean).

`exists_normalSource_domination` starts with integral Noetherian schemes
`P,S,Q`, normal `S,Q`, and `topologicalKrullDim Q ≤ 2`.
The maps `b : S ⟶ P` and `q : Q ⟶ S` are proper and dominant with invertible
original function-field maps. The original base `P` has dimension at most
two and Nagata nonempty affine charts.

It constructs `T`, `beta : T ⟶ S`, `a : T ⟶ Q` and a finite
`NormalizedPointBlowupChain beta`, with `a ≫ q = beta`.
The terminal is integral, normal, Noetherian and of dimension at most two;
both maps are proper, dominant and birational through their original
function-field maps.

The proof first establishes finiteness of `contractedCurves q`.
`SelectedElimination` constructs a finite block whose proper-image curve
embedding omits a selected curve, giving strict decrease of the finite count.
The recursion composes those comparisons and their literal chains. At zero
count, the proper-birational isomorphism theorem supplies the actual inverse
of `q` and the reflexive chain.

The general `NormalizedPointDomination.exists_domination` wrapper first takes
the finite generic normalization of a potentially nonnormal supplied model.
Thus source normality belongs to this induction, not to the final domination
interface. No terminal regularity is asserted.

Present consumers: [Birational/NormalizedPointDomination](../NormalizedPointDomination.md).
