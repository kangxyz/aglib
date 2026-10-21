# Flat base change of actual ideal modules

`Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.FlatMorphism` supplies
`Scheme.Hom.idealPullbackMap_isIso_of_flat`. For schemes in the same universe,
consider a displayed cartesian square

```text
D' --a--> D
 |        |
i'        i
 |        |
 v        v
 X --b--> S.
```

If `i` is affine and `b` is flat, the existing canonical map
`idealPullbackMap i i' b a h : b* (idealModule i) ⟶ idealModule i'` is an
isomorphism. Here `h : a ≫ i = i' ≫ b`; both ideal modules are the actual
kernels of the original structure-module maps. No closed-immersion,
Noetherianity, rank-one, or quotient-flatness hypothesis is needed.

The proof first treats the literal pullback of `i` and `b`. The canonical
affine structure-module base-change map is adjoint to the original
`squareStructureModuleMap`. Its compatibility with the structure maps and the
canonical unit comparison gives a square of isomorphisms. Flat pullback
preserves its actual kernel, so the induced kernel isomorphism equals the
original `idealPullbackMap`, as checked after composing with the original
ideal inclusion. The general displayed square follows through its canonical
isomorphism to that literal pullback.

The lower leaves are the existing affine module base-change theorem and exact
pullback along a flat scheme morphism. The separate
[`BaseChange.Flat`](Flat.lean) theorem assumes that a quotient is flat over a
further base and allows arbitrary change of base; its premise is not used here.

The consumer is the literal DVR residue-field fibre in
[`Cartier.DVRFibre`](../Cartier/DVRFibre.lean). The new proof is authored against
Aglib source HEAD `3a4d549981ced306d89d3ed55418c9e6a25f86c4`, Lean 4.34.1,
and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. Native compilation
evidence is returned separately and is scoped to the actual source hashes.
