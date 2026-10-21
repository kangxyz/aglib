# Field-valued polygon lifts

[CoverPoints.lean](CoverPoints.lean), in
`AlgebraicGeometry.Scheme.Polygon`, constructs actual lifts through the
canonical projection of [Projection.lean](Projection.lean).

For fields `k, K : Type u` and `NeZero n`, every morphism
`p : Spec K ⟶ PinchedLine.pinchedGluing k` has a morphism
`s : Spec K ⟶ cycleScheme k n` satisfying `s ≫ cycleMap k n = p`.
`fieldPointLift` chooses such a lift, and `fieldPointLift_map` and
`fieldPointLift_over` give its projection and coefficient-structure triangles.
The statement concerns the original field, without an extension or algebraic
closure. It assumes no invertibility of `n` and no universal patching family.

`polynomialRingMap_lift` lifts a field-valued pinched polynomial-ring map to
the actual normalization. A map killing the conductor equals node evaluation;
a map not killing it uses `conductorLocalizationEquiv`. Evaluation on the
first actual component gives `affineRingMap_lift` and its scheme version.
`infinitySection` is first-component evaluation on the native split infinity
algebra. The two exhaustive target opens then give the global field-point lift.
Positivity enters only when choosing the first component `0 : Fin n`.

## Source correspondence

Frozen R5 revision `f8a3314ddecffcada2ec721d26d56a937bed9690`,
`R5Lab.AlgebraicGeometry.Curves.Cyclic.Covers.FiniteCover`, lines 488–590,
SHA-256 `b96dbafa96b00d65651d1f9b2e777bc889c72e9e02c218b154c2a17813a33f37`.
All public declaration basenames are retained under the native polygon namespace.

| Frozen source lines | Native declarations |
|---|---|
| 488–516 | `polynomialRingMap_lift` |
| 517–524 | `affineRingMap_lift` |
| 525–534 | `affineMap_fieldPoint_lift` |
| 535–542 | `infinitySection`, `infinitySection_map` |
| 543–573 | `cycleMap_fieldPoint_lift` |
| 574–590 | `fieldPointLift`, `fieldPointLift_map`, `fieldPointLift_over` |

The authorized prerequisite is only `DoubleCoverPoints.lean`, lines 38–66,
SHA-256 `400f6ec15d26fd74b56c2c4b5fd52bc0b523a9095d2a27867d5f1c02bda18487`:
its five node-evaluation declarations become private
`Polynomial.PinchedPair.fieldNodeEvaluation`,
`fieldNodeEvaluation_conductor`, `fieldNodeEvaluation_second`,
`fieldEval_second_eq_zero`, and `fieldEval_eq_nodeEvaluation`.
These helpers preserve independent field universes `u` and `v`, with the
supplied `Algebra k K`. They use the existing native `coordinate_relation`,
`coordinateHom` and `coordinateHom_surjective`. No marked double-cover model
or downstream arithmetic endpoint is imported.

The input basis is the same original author snapshot recorded by
[EtaleProjection.md](EtaleProjection.md). The native client
[AglibTest.PolygonFiniteCover](../../../../../AglibTest/PolygonFiniteCover.lean)
exercises the literal maps at level two over `ZMod 2`, arbitrary field-valued
lifts, and the finite étale rank-zero case.
