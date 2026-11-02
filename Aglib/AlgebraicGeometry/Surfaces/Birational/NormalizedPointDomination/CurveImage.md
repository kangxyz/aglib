# Proper images of curves on different models

Source: [CurveImage.lean](CurveImage.lean).

For proper `f : X ⟶ Y`, `f.irreducibleClosedImage C` is the closed set
`f '' C` for `C : IrreducibleCloseds X`. Its generic point is the image of
the original generic point of `C`.

Assume `X,Y` integral, `Y` locally Noetherian and normal of dimension at most
two, and `f` proper, dominant, with invertible `functionFieldMap f`.
`irreducibleClosedImage_injective_of_not_subsingleton` proves uniqueness of
a closed irreducible subset with a specified nonsubsingleton image.
`dimension_irreducibleClosedImage_eq_one` gives image dimension one if the
source subset avoids the generic point and its image is nonsubsingleton.
The codimension-one isomorphism locus and uniqueness above the target generic
point supply these statements without a source dimension or regularity bound.

`genericPoint_not_mem_contractedCurve` proves the required generic-point
avoidance for contracted curves. For `p : X ⟶ S` and `g : X ⟶ Y`
proper dominant birational, assume integral `X,Y,S`, normal locally
Noetherian `Y,S` and `topologicalKrullDim Y ≤ 2`.
For any `q : Y ⟶ T` and `r : S ⟶ T` with `g ≫ q = p ≫ r`,
`irreducibleClosedImage_mem_contractedCurves` retains contractedness of a
noncollapsed image. `contractedCurveImageEmbedding` is defined on precisely
those curves whose images are nonsubsingleton; `Noncollapse` supplies that
condition for finite common graphs.

This is the codimension-one image step in
[Stacks tag 0BBT](https://stacks.math.columbia.edu/tag/0BBT).

Present consumers: [CurveOrder](CurveOrder.md), [CurveResidue](CurveResidue.md), [CurveStalk](CurveStalk.md), [Noncollapse](Noncollapse.md).
