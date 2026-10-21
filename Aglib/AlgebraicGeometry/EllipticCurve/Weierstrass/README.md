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
| [GeometryInputs](GeometryInputs.lean) | Stable exact interfaces for nonsingular geometry and arbitrary pointed-projective j-invariance. |
| [Geometry](Geometry.md) | Over every field, nonzero discriminant gives the actual smooth proper genus-one curve; geometric integrality and constants hold for every equation. |
| [Normality](Normality.md) | Over a domain DVR, nonzero generic discriminant gives normal stalks of the same literal projective cubic, including singular residue fibres. |
| [Genus](Genus.md) | Actual structural-field H¹ is linearly isomorphic to the field, including singular cubics. |
| [Genus/Charts](Genus/Charts.md) | Monic chart bases, actual overlap restrictions and the one-dimensional Laurent quotient. |
| [PoleBasis](PoleBasis.md) | Intrinsic principal-ideal colength forces triangular coordinates for every affine algebra isomorphism over a field. |
| [PointedIsomorphism](PointedIsomorphism.md) | Every origin-preserving isomorphism of the literal nonsingular cubics preserves j, over every field. |
| [PointedGroup](PointedGroup.lean) | Adapter to the native genus-one group construction, retaining its Picard representability and other explicit prerequisites. |
| [CoordinateGroup](CoordinateGroup.lean) | Stable operation-comparison interfaces and group-homomorphism bundling for a given pointed group law. |
| [GroupCompatibility](GroupCompatibility.md) | The original characteristic-zero coordinate addition comparison for every given pointed group law, including its original-group points over any field extension. |

The common affine coordinate and lift definitions are imported from
[Affine.Coordinates](../Affine/Coordinates.lean). The general homogeneous quotient
grading belongs to [GradedAlgebra.Quotient](../../../RingTheory/GradedAlgebra/Quotient.lean).
General extension from actual valuation-ring stalks belongs to
[Proper.GenericExtension](../../Morphisms/Proper/GenericExtension.lean).
[Curves.GenericExtension](../../Curves/GenericExtension.lean) proves the exact
normal smooth-curve extension family over arbitrary fields and preserves both
the structural and generic-stalk triangles.

The exact retained geometry, pointed-isomorphism and operation-comparison
families now have proved suppliers in the modules above. The j-invariance
proof derives an admissible variable change from the actual pointed
isomorphism. Coordinate addition is compared with the given group law and,
after any field extension, with the original group's point functor. The
genus computation concerns coherent arithmetic genus, including singular
cubics; it does not compute the genus of their normalizations. The native
genus-one group construction retains its Picard representability input.

The ordinary R5 packet files `Curves.GenericExtension` and
`EllipticCurve.Weierstrass.{Projective,Points,CofinitePoints,VariableChange}` are
the extraction basis. Application-specific `GeometryBackground` and
`EllipticScheme` adapters remain downstream. No analytic imports, arithmetic
markings, Tate parameter or application identity is introduced here.

Focused interface guides: [Coefficient base change and residue fibres](BaseChange.md), [Split critical cubics](CriticalCubic/README.md), [Actual extension points under coefficient-fixing automorphisms](ExtensionPointAction.md), [The actual smooth charts of a Weierstrass cubic](SmoothLoci.md).
