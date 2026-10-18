# Multilinear maps

[Span](Span.lean), imported as `Aglib.LinearAlgebra.Multilinear.Span`, supplies
`MultilinearMap.map_mem_span_of_forall_mem_span`: for a commutative semiring `R`, a multilinear
map `f` in finitely many variables (`[Finite ι]`) sends a family of vectors of `span R T` into
the span of the values of `f` on families of vectors of `T`. The modules are arbitrary; no
finiteness of `T` or of the modules is assumed.

The lower prerequisite is Mathlib only. The present consumer is the multilinearity step of the
[Fitting ideals](../../RingTheory/FittingIdeal/README.md) (`Submodule.span_minorIdeal`).
