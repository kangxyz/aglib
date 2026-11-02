# The native extension of an original degree-one linear equivalence

Over any commutative semiring, with independent universes for coefficients
and both arbitrary variable types, `degreeOneLinearMapAlgHom` evaluates on
the images of the existing original-variable homogeneous degree-one basis.
Its restriction is exactly the supplied linear map. Extending the inverse
linear equivalence gives the inverse polynomial algebra map, using native
`AlgEquiv.ofAlgHom`, not another polynomial or symmetric-algebra model.

`degreeOneLinearEquivAlgEquiv` preserves every original homogeneous degree
by the existing `IsHomogeneous.aeval` theorem. There are no field,
nontriviality, finite-variable or equal-variable-universe assumptions.
The actual cotangent-basis comparison is a downstream consumer.
