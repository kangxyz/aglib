# Finite elimination of a selected contracted curve

Source: [SelectedElimination.lean](SelectedElimination.lean).

`exists_comparison_missing_curve` assumes integral Noetherian `P,S,Q`,
normal `S,Q`, `topologicalKrullDim Q ≤ 2`, and proper dominant birational
maps `b : S ⟶ P`, `q : Q ⟶ S`. The original base `P` has dimension at most
two and Nagata nonempty affine charts. Given `C : contractedCurves q`,
it constructs `B : NormalPointComparison q` such that `C` is absent from
the range of its derived curve embedding.

The original curve residue supplies a transcendental element and the
birational field map supplies its fraction. Strong induction on the minimum
of the numerator and denominator's finite DVR orders constructs the block.
At each step it blows up the actual closed image point and normalizes,
constructs the normal common graph component, and derives noncollapse.

If the curve survives, the projection identifies its generic stalk through
the original stalk-map isomorphism. `SelectedStep` divides the retained
fraction by the same exceptional generator and strictly decreases both
orders. The recursion composes the original diagrams and chains;
`missing_curve_comp` preserves the omitted curve.

The finite block, curve embedding and strict decrease are constructed.
`CardinalityInduction` uses this result for the outer finite-count induction.

Present consumers: [CardinalityInduction](CardinalityInduction.md).
