# Actual graph-closure comparisons

Import `Aglib.AlgebraicGeometry.Morphisms.Proper.GraphClosure.Comparison`.

The objects remain those of `Scheme.GraphClosure`: the native schematic
image of the original graph in the literal fibre product, with its original
source and target projections. The base scheme is arbitrary.

Suppose the target structural map is proper, the source open immersion is
quasi-compact, and a specified cartesian square identifies that open with
the source's base change along `j : T ⟶ S`. `baseChangeSourceIso` gives an
isomorphism from the literal base change of the graph closure to the
literal base change of the source. Its forward map is exactly the native
base change of the original source projection, as stated by
`baseChangeSourceIso_hom`.

Write `H` for the specified cartesian square. Let `e` be an isomorphism
in `Over T` of the source and target base changes, and assume the original
partial graph map is induced by this same isomorphism:

```lean
h = H.isoPullback.hom ≫ e.hom.left ≫ pullback.fst g j
```

Under this compatibility hypothesis, `baseChange_overTarget_eq` retains
the original target projection. Both original projections are then
isomorphisms after this base change.

`liftFromDense` assumes that `j` is scheme-theoretically dominant and that
the supplied map into the fibre product factors through the original
open graph after composition with `j`. It derives containment of the
actual ideal kernels and uses the native universal property of the closed
image inclusion. The resulting morphism into the actual graph closure
retains the original fibre-product map and both projection triangles.
This supplies the section-lifting step for the trait application.

This file does not assert regularity of the graph closure.
