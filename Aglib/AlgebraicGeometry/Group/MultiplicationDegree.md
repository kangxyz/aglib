# Multiplication has degree the square of its level

`MultiplicationDegree.lean` supplies the missing degree producer for
`packet/AGLIB_TASKS_ETALE_GROUPS.md`, row `EG-MULTIPLICATION`.
For every field `k`, actual `G : Grp (FScheme k)`,
`hG : Scheme.OverField.Curve.Properties G.X`,
`hg : Curve.coherentGenus k G.X = 1`, and `hn : IsUnit (n : k)`,
the theorem
`Scheme.Group.Multiplication.multiplication_finite_etale_degree`
proves

```text
IsFinite ((𝟙 G.X) ^ n).left ∧
Etale ((𝟙 G.X) ^ n).left ∧
HasGeometricDegree ((𝟙 G.X) ^ n) (n * n).
```

`multiplication_hasGeometricDegree` is the degree conjunct alone.
`multiplication_nativeRank` proves
`((𝟙 G.X) ^ n).left.finrank y = n * n` at every actual point `y`.
The morphism is the literal power in the original group law. Geometric
degree retains every algebraically closed same-universe field, every
structural field map and every point of the target. No characteristic-zero
or perfect-field restriction occurs. Invertibility already excludes level
zero; the original positive-level target is therefore included.

The coherent-genus-one premise is explicit, matching the elliptic source
accepted in the continuation brief. This module does not derive genus one
solely from a proper smooth connected group curve. It assumes no
Riemann–Roch, norm/order, square/cube, Picard-duality or representability
theorem family: the needed existing families are bound to their proved
native suppliers.

The geometric argument uses the actual identity ideal class `I` and
the actual difference morphism `δ : G × G → G`. Its fibre over the identity
is the diagonal, and `(δ, pr₂)` gives product coordinates. The native
Cartier ideal base-change map therefore identifies `δ*I` with the diagonal
ideal. Inversion fixes `I`. Consequently the Picard class

```text
P = -δ*I + pr₁*I + pr₂*I
```

is symmetric, and its diagonal pullback is `2 • I`. The file proves that
`P` is precisely the existing normalized Abel class of the identity
morphism. The independently constructed group-law bridge in
`PointDivisor.lean` proves `(id × [n])*P = n • P`. Symmetry gives the same
scaling in the first coordinate. Pulling back along the diagonal yields
the actual class equality `[n]*(2 • I) = (n*n) • (2 • I)`.

The existing finite-Cartier degree theorem gives `deg(I) = -1` from the
actual rational identity section. Native curve pullback-degree scaling,
applied to the already proved finite-etale map, forces its locally free
rank to be `n*n`. This first computes the rank over an algebraically
closed base field. For the original arbitrary field, the actual
algebraic-closure base change is identified with the same multiplication
power; coherent genus is preserved, and native finite-flat rank descends
through the surjective projection. The existing geometric-fibre rank/card
comparison supplies the full geometric point count.

The frozen source target is
`R5Lab/AlgebraicGeometry/EllipticCurve/Isogenies/CyclotomicDualKernel.lean`,
lines 283–286, at R5 revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`; its packet SHA-256 is
`9e41c9cb806d7b989f7827341fb0c9e54fbcc2276d8f006efcc11b17aedb99a4`.
That file states `EllipticMultiplicationGeometry` as a theorem-family
boundary. The new producer does not take that family as an input.

Relevant source identities are:

| Source | SHA-256 |
|---|---|
| `MultiplicationDegree.lean` | `93699d2a28331bd47324817b644463f0f3e45b498f5156cf038912fb59b36db1` |
| `PointDivisor.lean` | `4e875fa90edb639e9a5d9449ed31dc8a4561bc9d5754f9c347c1c275cb0670bb` |
| `MultiplicationInvertible.lean` | `f2c8a8030e3fa27b0656c34d9f6ee3b5d877a8d171b49d2c38edef06a2c28e9b` |
| `../Curves/Abel/FiniteCartierDegree.lean` | `033b02cc546a2265264e16cbc7bd4809dc1a924989e52df790d7341be6549de6` |
| `../Curves/Picard/NormDegree/OrderFormula.lean` | `1259c1361b1898d8d6a9ef7b81a395e92cf3ce36d4175ee1a10ff025edaeda9a` |

Rank-two torsion and the perfect pairing remain separate
consumers and are not proved by this module.

The native coherentGenus = 1 hypothesis remains explicit. An external source genus field requires a separate identification; no unrestricted packet-family or bare curve-group genus theorem is inferred here.
