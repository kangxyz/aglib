# Artin–Schreier sequence and root covers

The lower ring owner [ArtinSchreier](../../../RingTheory/Etale/ArtinSchreier.lean)
defines the actual quotient `R[X] / (X^p - X - a)` for prime `p`. It is finite
and free over every commutative ring `R`, and the structural scalar action is
faithful. When `(p : R) = 0`, the quotient is étale; the premise includes the
zero ring.

[RootCover](RootCover.lean) constructs, for any scheme `X` and
`a : Γ(X, ⊤)`, the actual scheme root cover. Under `(p : Γ(X, ⊤)) = 0` it is
finite, étale and surjective, and its global sections contain an original
`b` satisfying `b^p - b = f.appTop.hom a`. The construction also applies when `X` is empty. The completed additive
coefficient sequence is described below.

## Additive sheaf sequence

For every `X : Scheme.{u}`, prime `p`, and literal equation
`(p : Γ(X, ⊤)) = 0`, the actual small-etale sheaves form the short exact sequence

```text
0 → constant(ULift(ZMod p)) → additiveStructureSheaf X
    --(F - id)→ additiveStructureSheaf X → 0.
```

The isomorphism `primeFieldArtinSchreierKernelIso` identifies the constant
sheaf with the native kernel of `F - id`. Its hom is the literal `kernel.lift`
of the original coefficient inclusion. Coefficients are in
`AddCommGrpCat.{u+1}`. This includes empty
schemes and needs no affine, nonempty, Noetherian, exact-characteristic, or
Ext premise beyond the displayed equation.

| Source | Consumer interface |
| --- | --- |
| [Complex](Complex.lean) | The original inclusion, native Artin–Schreier map and their zero composite. |
| [Kernel cover](KernelCover.lean) | The root opens used for local surjectivity. |
| [Short exact sequence](ShortExact.lean) | Epi, native-kernel isomorphism and exactness of the original complex. |

The supplier root compiled at standard 200000 heartbeats and passed independent
mathematical review. Native integration passed the affected build and existing
consumer graph, generated entries, text style, all 15 declaration linters, and
the 653-declaration axiom audit with only the three standard foundations.
This result does not prove affine-etale acyclicity, the curve calculation,
proper base change, or unbounded six operations.
