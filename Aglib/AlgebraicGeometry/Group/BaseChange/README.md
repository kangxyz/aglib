# Base change of marked kernels

`MarkedKernel` extends the canonical
`AlgebraicGeometry.Scheme.Group.BaseChange` implementation from
`Aglib.AlgebraicGeometry.Group.ScalarExtension`. It transports the actual
universal kernel marking and torsor-action data through arbitrary scheme base
change; it does not reconstruct the lower group-scheme base-change object.

The source's complete universe, base, finite/etale/surjective and marking
hypotheses remain attached to each declaration. Current consumers are general
group-scheme monodromy and downstream pointed-cover applications. Historical
elliptic terminology in source provenance does not add an elliptic premise to
the admitted general declarations.
