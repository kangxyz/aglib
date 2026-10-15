# Factorization through good lower truncation

[TruncGE](TruncGE.lean), imported as `Aglib.Algebra.Homology.Embedding.CochainComplex.TruncGE`, gives `CochainComplex.fromTruncGE`. For an actual map `f : L ⟶ K` of integer cochain complexes in an arbitrary abelian category and `[K.IsStrictlyGE a]`, it constructs a map `L.truncGE a ⟶ K`.

`πTruncGE_fromTruncGE` states that precomposition with the actual good-truncation projection recovers `f`. The target's strict lower term bound is retained. The original scheme statement is the explicit specialization to `X.Modules`, not an assertion about an arbitrary replacement/model of the complex.

[Stupid truncation layers](../StupidTrunc/README.md) have different objects/maps. Bounded-below factorization and the selected generic derived/Godement consumers use this good-truncation interface.
