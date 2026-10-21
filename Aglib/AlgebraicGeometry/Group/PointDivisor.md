# Actual point/divisor compatibility

`PointDivisor.lean` connects the existing normalized degree-zero Abel class
to the supplied group law on the original curve. Its consumers are
`MultiplicationDegree.lean` and the point/divisor identification needed by
Cartier duality.

The native abbreviation `degreeZeroPointClass G hG T f` is the existing
`Curve.Abel.degreeZeroAbelClass`, with its proved native geometric and
Cartier suppliers. It introduces no alternative Picard group, divisor class
or degree.

For an algebraically closed field of arbitrary characteristic, actual
`G : Grp (FScheme k)`, `hG : Curve.Properties G.X`, and
`coherentGenus k G.X = 1`, the native theorems prove, on every test scheme `T`,

- `degreeZeroPointClass_mul`: `A(f * g) = A(f) + A(g)`;
- `degreeZeroPointClass_pow`: `A(f ^ n) = n • A(f)` for every natural `n`.

No reducedness or Noetherianity is required of `T` in these two conclusions.
The preliminary `pointClass_injective_of_isReduced` works over an arbitrary
field and every reduced test scheme, retaining the existing explicit
geometric, Riemann–Roch and cohomology families in its generic signature.

The proof uses the original evaluation-divisor `inverseCandidate` and
`inverseCandidate_class` only on the locally Noetherian product `G.X ⊗ G.X`.
Equality of Abel classes is first shown to detect scheme morphisms from a
reduced source by testing the actual residue-field maps. This identifies
the two axis restrictions of the recovered sum morphism. Proper product
rigidity then identifies that morphism with the literal multiplication
`μ[G.X]`. Naturality transfers the class identity to every test scheme.

The native bindings use the proved smooth normality, regularity and
dimension suppliers, normal-component openness, proper-curve product
formula, tensor pullback, finite-Cartier ideal degree, Cartier base change,
finite-morphism norm/order, proper structure-cohomology base change,
Riemann–Roch, high-degree vanishing, Noetherian cohomology vanishing and
fibrewise Cartier regularity. No representing witness or
`DegreeZeroPicardRepresentability` parameter is used.

Native supplier source identities:

| Input | SHA-256 |
|---|---|
| `Curves/Abel/Inverse.lean` | `4b50bd0a16558a6a9cf520f320c926e67672b9191a989c535dae62ae0e46e7ab` |
| `Curves/Abel/Injectivity.lean` | `7de2c2b4c7a48290ede2efcb8f9f2825afa3d4b36216b8875d6356b0b0623540` |
| `Group/PointedMorphism.lean` | `c5537cd9e9dca2ab3b591ae2edf8a36399fe0066f7779e19cd3d8b90ebc70324` |

The native coherentGenus = 1 hypothesis remains explicit. An external source genus field requires a separate identification; no unrestricted packet-family or bare curve-group genus theorem is inferred here.
