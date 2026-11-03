# Original associated-graded and canonical-kernel transport

`Ideal.associatedGradedEquiv e I` uses the stock ideal quotient equivalence
on the single existing Rees coefficient map promoted by `reesAlgebra.mapEquiv`.
Its target is exactly the associated graded of the original image ideal.
The associated-graded defining ideal is transported by its actual original
scalar map, and original Rees classes retain their literal map equation.

`cotangentPolynomialMap_equiv_square` proves the whole RingHom square for
arbitrary generators of the original ideal. Both the original quotient
coefficient map and actual degree-one Rees symbols commute. The entire kernel
identity follows from that square and actual injectivity; no chosen relation
or desired tangent-kernel equality is assumed. The `_of_eq` wrapper identifies
the image ideal with any explicitly equal original target ideal.

Source and target ring universes and generator-index universe are independent.
Only commutative ring and actual ring-equivalence hypotheses are used. The
native associated-graded quotient and grading are unchanged; this is not a
second associated-graded implementation. Local maximal-ideal and original
residue-map specialization belongs to the marked-data consumer.
