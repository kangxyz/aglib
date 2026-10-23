# The original base cover for proper contraction

`Proper.image_isClosed` proves that the constant image of a nonempty closed
subscheme under the original proper map is a closed singleton. No chosen
residue-field identification is needed.

`Proper.exists_affine_base_cover` chooses an actual affine neighbourhood `V`
of that image and the open complement `Z` of its singleton. It proves the
base covering equation, containment of the same exceptional projective line
in the actual inverse image of `V`, and containment of the inverse image of
`Z` in the original exceptional complement. It also proves that the inverse
image of `V` and that original complement cover the source.

`exists_cartier_contraction_of_local_projective_embedding` assembles the actual
contraction over the original base from a finite projective embedding of the
specified inverse-image neighbourhood. It preserves the same exceptional curve,
full field point, original Cartier ideal, canonical blowup lift, complement and
structural triangle. The intermediate coefficient field is not identified with
the residue field of the base image.

`dimension_eq_two_of_point_complement` recovers dimension two from the constructed
point stalk and actual complement isomorphism when the original source has
dimension at most two. It uses the original stalk maps, without a dimensional
descent assumption on the proper map.

`birationalOver_of_point_complement` constructs the actual partial isomorphism
over the original target. The point-stalk dimension makes its target complement
dense, and surjectivity makes its original source complement nonempty and dense.
Properness of the structural map also supplies separatedness over the same base.

The general proper existence theorem still requires the forward projective
construction to produce that local embedding. This leaf does not claim that
remaining projectivity premise closed.
