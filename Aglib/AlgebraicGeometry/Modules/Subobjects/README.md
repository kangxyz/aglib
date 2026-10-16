# Gluing module subobjects

[Gluing](Gluing.lean), imported as `Aglib.AlgebraicGeometry.Modules.Subobjects.Gluing`, defines
`Scheme.Modules.subobjectObstruction` from the cokernel of an open subobject and the actual
restriction/direct-image adjunction. Its counit equation recovers the original cokernel map;
the original local monomorphism is its restricted kernel.

Compatible subobjects on two open immersions are glued by the kernel of the pair of
obstructions. `exists_glued_subobject` retains both local restriction isomorphisms and the
equations with their original inclusions into the ambient module. The overlap comparison
uses the same chosen pullback and its two projections. The two opens need not cover the
scheme, and no quasicoherence, finite-type or Noetherian hypothesis is imposed here.

[Quasicoherent subobjects](../QuasiCoherent/Subobjects/README.md) supplies the corresponding
quasicoherence results with their additional premises.
