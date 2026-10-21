# Absolute inertia and normalization over a normal curve

`NormalCurveInertia.lean` proves the ordinary normal-curve interface for the
actual normalization of an original finite-etale generic cover. Its native
namespace is `AlgebraicGeometry.Scheme.FiniteEtale`; its client is
`AglibTest.NormalCurveInertia`.

The extraction basis is revision
`f8a3314ddecffcada2ec721d26d56a937bed9690`:

| Source module | Source range | SHA-256 |
| --- | --- | --- |
| `R5Lab.Aglib.AlgebraicGeometry.Morphisms.Etale.InertiaPurity` | 27–37 | `0e2fa717bcd9ee609e8c4921a1489aca32439466cfc274b03365e2368bc6b8f4` |
| `R5Lab.Aglib.AlgebraicGeometry.Morphisms.Etale.NormalCurvePurity` | 33–66 | `b7b4a2014cfc7dfed510e7d0874cdf7f9d50cbd1c5085c5c85b18721aaf57153` |

`NormalCurveCoverPurity` retains integral Noetherian `X`, integrally closed
actual target stalks, dimension at most one, the original finite-etale cover
`C`, and a prime `Q x` of the integral closure of each actual codimension-one
stalk in `AlgebraicClosure X.functionField`. Every `Q x` must lie over that
stalk's actual maximal ideal. Fixedness quantifies over every element of its
absolute inertia subgroup and every geometric point of the original `C`.
The conclusion is etaleness of the actual native `.fromNormalization` map.

`divisor_closure_etale_of_original_points_fixed` retains the source's locally
Noetherian variant, original chart algebra, supplied prime and its lying-over
condition. It applies
`integralClosure.Inertia.Inseparable.model_etale_of_algebraicClosure_inertia_trivial`
to the actual divisor DVR and actual function field. `chartAlgebraPoint` and
`chart_embeddings_fixed_of_points_fixed` turn the original fixedness premise
into the theorem's fixedness condition for every embedding. The local-pullback
square then transports the resulting literal closure's etaleness to the actual
normalization pullback. The proved `normalCurveCoverPurity` term uses these
results and the dimension-zero/dimension-one geometric argument; the interface
is not supplied as an input to its own producer.

The actual accepted author-checkout supplier is
`Aglib/RingTheory/IntegralClosure/Inertia/Inseparable.lean`, SHA-256
`787b8388e7ed039670595b57802519e97712f8b655d200bb4f3eb6729d2f1c2c`.
The disposition packet names release-copy hash
`bfa0b3b5e29a1f5727925642d676b31cc56c9493748793da18455d4dbb83dee2`;
that copy is not the compilation input for these new files. The principal
explicitly accepted the frozen author supplier and its actual API. Its criterion
retains a domain DVR `R`, fraction field `K`, etale original `K`-algebra `A`,
the exact scalar tower, the actual prime of `integralClosure R (AlgebraicClosure K)`,
its lying-over-maximal-ideal condition, and fixedness for every inertia
automorphism and every `K`-algebra embedding of `A` into that algebraic closure.

Arbitrary residue fields, all characteristics, and empty or split covers are
allowed. This result does not instantiate regular-surface Zariski–Nagata purity
or Stacks `0BMB`; no global torsor realization, H1 statement, arithmetic marking
or application theorem is in this leaf.
