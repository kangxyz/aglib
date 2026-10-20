# Literal Weierstrass schemes, charts and points

These modules use Mathlib's `WeierstrassCurve`, `VariableChange`,
`Affine.CoordinateRing` and coordinate points. `Projective` constructs the actual
homogeneous-quotient `Proj` of that equation, with the corrected `a₄XZ²` term.
Its proper structure map and infinity section work over any commutative ring.

| Module | Construction or condition |
| --- | --- |
| [Projective](Projective.lean) | Quotient grading, literal Proj, proper structure map, standard charts and infinity section. |
| [AffineChart](AffineChart.lean) | Actual ring isomorphism from Mathlib's affine coordinate ring to the standard z-chart, and the open immersion. |
| [AffineComplement](AffineComplement.lean) | Over any field, the chart omits exactly the infinity point. |
| [Points](Points.lean) | Coordinate evaluation and the original rational-point maps. |
| [ExtensionPoints](ExtensionPoints.lean) | For every field map `k → K` and `Δ ≠ 0`, coordinate points are in bijection with K-valued points of the original k-scheme. |
| [AffineField](AffineField.lean) | Rank-two norm injectivity and the retained characteristic-zero quadratic existence argument. |
| [CofinitePoints](CofinitePoints.lean) | A nonzero affine function has finitely many coordinate zeros. |
| [PointedAgreement](PointedAgreement.lean) | Cofinite agreement with a homomorphism determines a proper-group morphism and forces its origin equation, under the stated group and geometric hypotheses. |
| [VariableChange](VariableChange.lean) | Actual affine-ring pullback and its inverse for an admissible variable change. |
| [VariableChangeChart](VariableChangeChart.lean) | The corresponding contravariant Spec isomorphism over the same field. |
| [FunctionField](FunctionField.lean) | Generic-stalk/affine-fraction-field equivalence with the actual x and y maps. Integrality is explicit. |
| [GeometryInputs](GeometryInputs.lean) | Exact unresolved nonsingular-geometry and arbitrary pointed-projective j-invariance inputs. |
| [PointedGroup](PointedGroup.lean) | Conditional adapter to the native genus-one group construction, retaining its actual prerequisites and the geometry input. |
| [CoordinateGroup](CoordinateGroup.lean) | Conditional group-homomorphism bundling; chord/tangent comparison remains an explicit input. |

The common affine coordinate and lift definitions are imported from
[Affine.Coordinates](../Affine/Coordinates.lean). The general homogeneous quotient
grading belongs to [GradedAlgebra.Quotient](../../../RingTheory/GradedAlgebra/Quotient.lean).
General extension from actual valuation-ring stalks belongs to
[Proper.GenericExtension](../../Morphisms/Proper/GenericExtension.lean).
[Curves.GenericExtension](../../Curves/GenericExtension.lean) proves the exact
normal smooth-curve extension family over arbitrary fields and preserves both
the structural and generic-stalk triangles.

The geometry, operation-comparison and arbitrary pointed-isomorphism assertions
are statements of the remaining supplier obligations. Their definitions do not
prove them. Mathlib's j-invariance under an admissible variable change does not
identify every pointed projective isomorphism with such a change. The native
genus-one group construction still retains its Picard representability input.

The ordinary R5 packet files `Curves.GenericExtension` and
`EllipticCurve.Weierstrass.{Projective,Points,CofinitePoints,VariableChange}` are
the extraction basis. Application-specific `GeometryBackground` and
`EllipticScheme` adapters remain downstream. No analytic imports, arithmetic
markings, Tate parameter or application identity is introduced here.
