# The normal common graph component

Source: [CommonModel.lean](CommonModel.lean).

Start with integral `X,Y`, proper maps `f : X ⟶ S`, `g : Y ⟶ S`,
a nonempty quasi-compact open `U ⊆ X`, an open immersion `h : U ⟶ Y`,
and the equation `U.ι ≫ f = h ≫ g`.
The component is the schematic image of this graph in the literal fibre
product `X ×[S] Y`. Both projections are dominant and their original
function-field maps are isomorphisms.

`CommonModel.model` is normalization of that component in its own generic
stalk. `toSource` and `toTarget` are its normalization map followed by the
original graph projections; `toSource_comp` retains their triangle over `S`.
The model is integral and normal, and both field maps remain isomorphisms.
If every nonempty affine chart of the component is Nagata, the normalization
and the pair into `X ×[S] Y` are finite, and both projections are proper.
Neither `X` nor `Y` is assumed normal.

The component choice matters: the full product of the two equal blowup charts
over `Spec k[x,y]` has ring `k[x,t,s]/(x(t-s))`, with a vertical component
as well as the dominating diagonal. The construction normalizes the
common-open graph component.

This is the common-model step of
[Stacks tag 0BBT](https://stacks.math.columbia.edu/tag/0BBT).
`CommonModelOverBase` derives the chart-finiteness conclusion from the
accumulated map to the original Nagata surface.

Present consumers: [CommonModelOverBase](CommonModelOverBase.md).
