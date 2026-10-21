# Finite étale polygon projection

[EtaleProjection.lean](EtaleProjection.lean) proves properties of the canonical
maps in [Projection.lean](Projection.lean), in
`AlgebraicGeometry.Scheme.Polygon`.

For every field `k : Type u` and natural `n`, the literal `baseMap`, `affineMap`
and `cycleMap` are étale. The global `cycleMap` is finite and flat, its native
`Scheme.Hom.finrank` is `n` at every target point, and the rank remains `n`
after every scheme base change in universe `u`. The same geometric-fibre
coordinate algebra has dimension `n` over every field `K : Type u` mapping to
the target, with its algebra structure from the actual pullback projection.
The over-field morphism has the original geometric-rank and geometric-degree
interfaces. The original `structureMap` is proper.

`NeZero n` is required for the connected-surjective packages and global
surjectivity. Finiteness, étaleness and the rank results include `n = 0`.
There is no characteristic or invertibility assumption on `n`.

The concrete conductor comparison uses
`RingHom.Etale.MilnorPatching.FiniteFree.etale_map` with `R = k[X]`, `S = k`,
`T = k × k`, index `Fin n`, `f = baseBoundary`, diagonal `g`, and
`e = boundaryTwist`. `normalizationBoundary_eq_compLeft` and
`nodeBoundary_eq_twisted_compLeft` preserve the exact native boundary maps:
the first branch at `i` takes the value at `(finRotate n).symm i`, and the
second branch uses `i`. `fiberBaseMap` is definitionally the supplier's map.
`baseFiberEquiv`, `cycleFiberEquiv` and `baseMap_eq_fiberMap` identify its
conjugate with the original diagonal `baseMap`. This removes the source's
universal `EtalePatching` premise for this concrete split-power application;
it does not prove that universal predicate for arbitrary conductor algebras.

Both global chart squares are proved cartesian using the exact principal-open
preimages and the canonical pushout projection. The finite étale category
object `finiteEtaleCycleCover` has literal hom `cycleMap`.

## Source correspondence

Frozen R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`,
`R5Lab.AlgebraicGeometry.Curves.Cyclic.Covers.FiniteCover`, 617 lines, SHA-256
`b96dbafa96b00d65651d1f9b2e777bc889c72e9e02c218b154c2a17813a33f37`.
The original namespace `Curves.LocalModels.CyclicAffine` becomes
`AlgebraicGeometry.Scheme.Polygon`; declaration basenames remain the same.

| Frozen source lines | Native declarations / treatment |
|---|---|
| 44–69 | `baseFiberRing`, `cycleFiberRing`, both diagonal squares, `fiberBaseMap` |
| 70–82 | `fiberBaseMap_etale`, supplied instead by the concrete proved finite-free theorem |
| 83–126 | `baseFiberEquiv`, `cycleFiberEquiv`, `baseMap_eq_fiberMap`, `baseMap_etale` |
| 141–152 | Existing canonical `Projection.affineMap` and finite/surjective properties reused |
| 153–162 | `affineMap_etale`, `actual_affine_cycle` |
| 176–224 | Existing canonical overlap/infinity/cycle maps and triangles reused; finite/étale infinity instances added |
| 225–359 | Both gluing ranges and overlap preimages, both global chart preimages and cartesian squares, `cycleMap_finite`, `cycleMap_etale` |
| 360–366 | Existing canonical `structureMap` reused; `structureMap_proper` added |
| 382–423 | Infinity/global/base-change rank, positive-level surjectivity and connected proper cover package |
| 438–470 | Actual over-field source/target/morphism, geometric-fibre rank and degree adapters |
| 607–614 | `finiteEtaleCycleCover` and its literal hom equation |

Authoring is bound to the original author checkout at HEAD
`3a4d549981ced306d89d3ed55418c9e6a25f86c4` and its live definitions. The
reconciliation packet's hashes describe later release files, not byte-identical
authoring prerequisites. In particular, original `Projection.lean` is
`0b4c674546e1090e92a0e325682fc289b24cbe25e6a4eb823eee8df4d299eba8`,
original polygon `Affine.lean` is
`4d1e8a79e0e972b2b7649a18d35ef29d293cad2064321820fba0dbd9c4670618`,
and the compiled original `MilnorPatching/Unramified.lean` supplier is
`b4ade8dfe501b41842ac4304850e86924c2f6afb42b00f4f512a762a3ff175d4`.
No original prerequisite is changed by this slice.
