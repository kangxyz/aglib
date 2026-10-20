# Homogeneous quotient gradings

[Quotient](Quotient.lean) constructs a grading on `A ⧸ I` from an existing
natural-number grading on a commutative algebra and a homogeneous ideal.
The degree-n component is the image of the original degree-n submodule under
the actual ideal quotient map. The direct-sum decomposition descends through
that same quotient, with both inverse identities proved.

The source is the reusable `GradedQuotient` section of the ordinary R5
`EllipticCurve.Weierstrass.Projective` packet file. The construction has no
curve, field, finite-type or nonsingularity assumption. Its first consumer is
the literal projective Weierstrass cubic.
