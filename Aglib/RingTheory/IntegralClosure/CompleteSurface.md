# Finite normalization of a complete normal local surface

`integralClosure.finite_of_complete_local_normal_dimLE_two` states finiteness
of the literal integral closure in every finite extension of the original
fraction field. The base is a complete Noetherian normal local domain of
dimension at most two. The statement retains its original coefficient map
and imposes no separability condition on the extension.

The [purely inseparable theorem](PurelyInseparable/CompleteLocalSurface.md)
uses the actual height-one residue layers. For the general case, embed the
given field in a finite normal hull. Its full automorphism fixed field is
purely inseparable over the original fraction field; the extension above
that fixed field is Galois. Normalize in the fixed field first, then use
separable trace-dual finiteness over that finite normal model.
[Integral-model comparison](FiniteOverNormal.md) keeps the same ambient
elements, and the actual embedding injects the originally requested
normalization into the finite larger one.

The pure-then-separable order avoids assuming completeness of an intermediate
normalization. It also avoids assuming Noetherianity or finite generation of
the requested normalization. The normal base hypothesis is essential to
this proof; the nonnormal case and the resolution applications remain
separate obligations. This new source is in native compiler iteration and
has no completion claim before successful compilation and correspondence.
