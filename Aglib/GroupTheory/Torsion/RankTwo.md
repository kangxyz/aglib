# Rank two from torsion cardinalities

[RankTwo.lean](RankTwo.lean) proves
`AddSubgroup.TorsionBy.nonempty_torsionEquiv_of_card` for any abelian group `T`
and positive natural number `n`. Its hypothesis is

```lean
∀ d : ℕ, d ∣ n → Nat.card (AddSubgroup.torsionBy T (d : ℤ)) = d * d
```

The conclusion is an additive equivalence between the actual subgroup
`AddSubgroup.torsionBy T (n : ℤ)` and `Fin 2 → ZMod n`.
`basisOfEquiv` converts such an equivalence into a basis for any existing
`ZMod n` module structure on its source. It uses the theorem that every additive
map of `ZMod n` modules preserves that scalar action.

The proof has three parts:

1. For a finite group `M` annihilated by `p ^ r`, the quotient `M / pM` and the
   kernel of multiplication by `p` have equal cardinality. If the latter has
   cardinality `p * p`, the quotient has a basis indexed by `Fin 2` over `ZMod p`.
   Lift its two basis vectors to `M`. Iterating the resulting expression
   `x = f a + p • y` exactly `r` times proves that the lifts generate `M`.
   The cardinality `(p ^ r) * (p ^ r)` then makes this surjection bijective.
2. `nestedLevelEquiv` identifies divisor-level torsion inside a torsion subgroup
   with the same divisor-level torsion in the original group. Every map preserves
   the underlying element. This supplies the prime-level hypothesis in part 1.
3. At coprime levels, the existing maps `coprimeTorsionLeft` and
   `coprimeTorsionRight` are jointly injective. CRT combines their two pairs of
   coordinates; the supplied cardinality proves bijectivity. Natural-number
   factorization assembles all positive levels. Level one uses the unique
   element of the actual subgroup and the zero coefficient ring.

Cardinality at level `n` alone is not a hypothesis sufficient for this result.
No finite-group classification, perfect pairing, or basis family is assumed.
The current geometric consumer is
[MultiplicationTorsion.lean](../../AlgebraicGeometry/Group/MultiplicationTorsion.lean),
which proves the entire divisor-cardinality family from actual multiplication
degrees.

The production module compiles with the package's standard `200000` heartbeat
budget. The assignment's scoped compilation covers this module and its imported
proofs; it does not assert independent mathematical review or additional lint,
test, or replay coverage.
