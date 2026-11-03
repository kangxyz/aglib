# Finite common graphs and noncollapse of curves

Source: [Noncollapse.lean](Noncollapse.lean).

Let `p : X ⟶ S`, `g : X ⟶ Y`, `r : S ⟶ T`, `q : Y ⟶ T` satisfy
`p ≫ r = g ≫ q`. Assume `p,r` proper and the pair
`pullback.lift p g w : X ⟶ S ×[T] Y` finite.
`closedPoint_comp_isFinite` and `closedFiber_toTarget_isFinite` prove that
the fibre over a closed `s : S` maps finitely to `Y`.
A curve contracted by both projections would lie in a discrete fibre and
be both irreducible and subsingleton, contrary to dimension one.

`finitePairContractedCurveEmbedding` additionally assumes integral `X,Y,S`,
normal locally Noetherian `Y,S`, proper dominant birational `p,g`, and
`topologicalKrullDim Y ≤ 2`. It embeds the entire `contractedCurves p`
into `contractedCurves q` by the original proper image under `g`.

The strict-count theorem further takes Noetherian `Y`, integral normal locally
Noetherian `T`, and proper dominant birational `q`. It proves finiteness
of the old curve set geometrically, finiteness of the new one by the
embedding, and strict count decrease when a specified old curve is omitted.
`SelectedElimination` constructs a finite block omitting that curve.

This is the finite-fibre image argument in
[Stacks tag 0BBT](https://stacks.math.columbia.edu/tag/0BBT).

Present consumers: [SelectedElimination](SelectedElimination.md).
