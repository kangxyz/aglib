# Rank two on the actual geometric torsion subgroup

[MultiplicationTorsion.lean](MultiplicationTorsion.lean) works with the literal
existing `MultiplicationKernel.finiteTorsionPoints E n`, the additive subgroup
of algebraic-closure-valued points killed by `n`.

The constructor `MultiplicationKernel.torsionBasis` has precisely these inputs:

- a commutative group object `E : Grp (FScheme F)` over a field `F`;
- `hE : Curve.Properties E.X`;
- `hg : Curve.coherentGenus F E.X = 1`;
- a positive natural number `n` and `IsUnit (n : F)`.

It returns

```lean
Module.Basis (Fin 2) (ZMod n) (MultiplicationKernel.finiteTorsionPoints E n)
```

`torsionModule` is the canonical scalar action obtained from the proved
annihilation by `n`. `torsionCoordinates` is the resulting linear equivalence
with `Fin 2 → ZMod n`. These constructions retain the original carrier and
point-group operations. The selected basis has no asserted Galois equivariance.
Level one is included: both the scalar ring and the torsion subgroup are trivial.

`torsionFibreEquiv` identifies this subgroup with the literal fibre over the
identity appearing in `HasGeometricDegree`. Thus `card_finiteTorsionPoints`
applies the proved `Multiplication.multiplication_hasGeometricDegree` directly.
For every divisor `d ∣ n`, `divisor_isUnit` supplies invertibility of `d` and
`card_torsionBy_divisor` applies the degree theorem at that divisor. The generic
[rank-two theorem](../../GroupTheory/Torsion/RankTwo.md) consumes this complete
family, rather than only the cardinality at `n`.

`torsionGaloisLinear` has exactly the underlying function of the original
`torsionGalois`. `torsionMapLinear d n hdn f` equips any existing additive map
between these actual torsion levels with semilinearity for
`ZMod.castHom hdn (ZMod d)`. Its underlying function is exactly `f`, so the
statement applies to the existing literal lowering and reduction maps without
altering them or choosing compatible bases.

The load-bearing geometric sources are
[MultiplicationDegree.lean](MultiplicationDegree.lean), SHA-256
`93699d2a28331bd47324817b644463f0f3e45b498f5156cf038912fb59b36db1`,
and its point/divisor source [PointDivisor.lean](PointDivisor.lean), SHA-256
`4e875fa90edb639e9a5d9449ed31dc8a4561bc9d5754f9c347c1c275cb0670bb`.
Their independent mathematical review is outside this authoring assignment.
Genus one remains an explicit premise; it is not inferred from a bare group
object and curve properties.

The production module compiles with the standard `200000` heartbeat budget.
The assignment's scoped compilation supplies no additional independent review,
standalone lint, test, or replay claim.
