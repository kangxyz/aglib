# Products of actual Cartier ideals

`Product.lean` constructs `Scheme.Hom.idealProductMap` by factoring the existing
`Cartier.idealMultiplication` through the actual kernel module of
`(i.ker * j.ker).subschemeι`. Its inclusion triangle is literal equality with
that existing multiplication.

The comparison is an epimorphism for arbitrary closed immersions: affine ideal
products consist of sums of products of the actual ideal sections. If the first
kernel module is locally rank one, exact tensoring makes multiplication a
monomorphism, and `idealProductIso` is the resulting isomorphism. The second
closed ideal need not be Cartier. This proves the unchanged
`Cartier.CartierIdealTensorProduct` family as a special case.

The proof uses no Noetherian or dimension hypothesis. The product ideal retains
its native scheme structure.

`ideal_mul_eq_inf_of_cartier_intersection` proves that the native product ideal
equals the native intersection if the first ideal is Cartier and the actual
intersection ideal on the second closed subscheme is Cartier. On affine
charts, the latter condition makes the image of the first principal generator
regular in the quotient section ring. Cancellation proves the ideal equality.
The condition on the intersection is retained in the exact
`Cartier.CartierSumIdealEqualsUnion` inhabitant. This stronger pointwise result
also does not require the second ideal to be Cartier on the ambient scheme.
