# Original scalar-extended Rees generators

[DegreeOneGenerators.lean](DegreeOneGenerators.lean) constructs the actual
linear map from an ideal `I` to the native Rees algebra, sending `b` to
the monomial `bX`. Its range is the original first homogeneous component.

`scalarDegreeOneMap` is the scalar extension of that original linear
map. Its domain is the full tensor module `S ⊗[R] I`; its target is the
full tensor algebra `S ⊗[R] reesAlgebra I`. The range theorem identifies
its image with the first component of the existing scalar-extended
grading. `scalarDegreeOneQuotient` retains this actual map with the
first component as codomain, and its surjectivity is proved.

`span_scalarDegreeOneMap` carries any specified spanning family of the
full tensor ideal to a spanning family of that first component. Together
with `baseChange_grading_one_pow`, including degree zero, it supplies
the hypotheses of the actual polynomial graded presentation in
`Proj.DegreeOneEmbedding`.

All original tensor coefficient and degree-one monomial maps remain
explicit. There is no flatness or injectivity premise and no passage to
the Rees algebra of the image ideal in `S`. The geometric comparison
with the original tautological coordinate row, and the assembly of a
finite standard projective embedding of a blowup chain, remain separate
obligations.
