# Algebraic categories and homology

[ModuleCat](Category/ModuleCat/README.md) supplies scalar restriction, localization, quotient-ring actions and canonical adjunction units on arbitrary modules. [FGModuleCat](Category/FGModuleCat/README.md) owns the actual finitely generated module category. Its abelian/exact structure uses Noetherianity; the objects and several scalar constructions are defined more generally.

[Homology](Homology/README.md) supplies quasi-isomorphism detection by an actual acyclic cone. [TotalComplex](Homology/TotalComplex/README.md) proves that rowwise quasi-isomorphisms of first-quadrant module bicomplexes induce a quasi-isomorphism of the native total complex, over an arbitrary ring and with independent module universe. Generic injective/Ext comparison belongs to [CategoryTheory/Abelian/Injective](../CategoryTheory/Abelian/Injective/README.md).

The consumers are actual quasicoherent/coherent sheaf functors and the scheme-cohomology comparison chain. Module paths use `Aglib.Algebra`; declaration owners include `ModuleCat`, `CochainComplex`, `HomologicalComplex₂` and `ComplexShape`.

[Polynomial/Laurent coefficient diagrams](Polynomial/Laurent/README.md) provide the actual scalar maps used by relative affine-space and coefficient base change. Generic [site module tensors](Category/ModuleCat/Sheaf/Tensor/README.md) lie below scheme-specialized tensor and projection-formula constructions.
