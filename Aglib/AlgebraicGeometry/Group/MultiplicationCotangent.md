# The actual first-order power formula

`MultiplicationCotangent.lean` proves the previously missing nonconstancy
obligation for the literal multiplication map `(𝟙 G.X) ^ n`. The source is a
native `Grp (FScheme k)`; its group law, origin, stalk ring and structural
constants are unchanged throughout.

For any `SmoothOfRelativeDimension d G.X.hom`, the file proves

```text
multiplicationCotangent G n = n • LinearMap.id
                            = (n : k) • LinearMap.id.
```

`multiplicationCotangent` is the actual pullback on the maximal-ideal cotangent
quotient at the identity. It is built from `Scheme.Hom.stalkMap`, transported
only by the point equality already proved in `multiplication_pointed`.
Equivalently, let `R` be that actual identity stalk and `m` its maximal ideal.
For the explicitly constructed `multiplicationLocalMap G n = φ_n`,
`multiplicationLocalMap_sub_natCast_mem_square` proves

```text
∀ a : m, φ_n(a) - (n : R) * a ∈ m ^ 2.
```

The proof uses the actual axes and projections of `G.X ⊗ G.X`. The native unit
laws show that restricting the group-law cotangent pullback to either axis is
the identity. The proved injectivity of the product axis map in
[RationalPoint.Cotangent](../RationalPoint/Cotangent.lean)
therefore identifies group-law pullback with the sum of the two projection
pullbacks. Functoriality gives the sum rule for a product of two actual pointed
morphisms. Induction on the literal power map then gives the scalar formula.
Neither commutativity nor a supplied differential formula is required.

When `0 < d` and `IsUnit (n : k)`, the same cotangent space has positive
dimension and multiplication by `n` acts nontrivially. The constant origin map
acts as zero. Hence `multiplication_ne_one_of_smooth_of_isUnit` proves that the
original `(𝟙 G.X) ^ n` is not the constant map `1`.

For the original `Curve.Properties G.X`, this discharges the nonconstancy
premise of `MultiplicationFinite.lean` and `MultiplicationEtale.lean`:

- `multiplication_finite_surjective_of_isUnit` proves finiteness and
  surjectivity over every field, from `IsUnit (n : k)`.
- `multiplication_finite_etale_of_isUnit` adds etaleness in characteristic zero.
- `multiplication_finite_etale_of_pos` obtains the characteristic-zero result
  directly from `0 < n`.
- The two `pointedGroupLaw_multiplication_*_of_isUnit` adapters retain the exact
  native group law stored by `PointedGroupLaw C c`.

The assigned target is the finite and etale part of
`EllipticMultiplicationGeometry` in
`R5Lab/AlgebraicGeometry/EllipticCurve/Isogenies/CyclotomicDualKernel.lean:283–286`,
at the supplied packet source SHA-256
`9e41c9cb806d7b989f7827341fb0c9e54fbcc2276d8f006efcc11b17aedb99a4`.
The earlier conditional producers retain their original interfaces; this file
supplies the missing premise. The earlier first-order/nonconstancy frontier is
therefore superseded by these proofs.

[MultiplicationInvertible](MultiplicationInvertible.lean) proves the finite-etale
conclusion in every characteristic from this same first-order calculation,
using the actual origin-stalk and generic-field maps. No degree
`n * n`, rank-two torsion basis, Weil pairing, Cartier pairing or Picard/Hilbert
representability statement follows from this file. The source-only client
`AglibTest/MultiplicationCotangent.lean` records the intended concrete kernel
consumer: the existing literal torsion carrier is finite for invertible levels,
and the existing kernel scheme is finite etale at positive levels in
characteristic zero. No client check was run; client checks and kernel replay
are prohibited by the current task instruction.
