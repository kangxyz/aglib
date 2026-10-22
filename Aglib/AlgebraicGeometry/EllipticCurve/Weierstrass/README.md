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
| [ProjectiveVariableChange](ProjectiveVariableChange.md) | The actual pointed projective isomorphism for each native admissible change over any commutative ring. |
| [Presentation](Presentation.md) | Over every field, a smooth proper geometrically connected curve of coherent genus one with its specified rational section admits a pointed isomorphism to a literal Weierstrass cubic with nonzero discriminant. |
| [SmoothDiscriminant](SmoothDiscriminant.md) | Actual relative smoothness of the literal projective cubic implies nonzero discriminant over every field. |
| [IntegralModel](IntegralModel.md) | Integral equations for a specified fraction-field equation, native DVR minima and pointed comparison by the same descended native change. |
| [GenusOneModel](GenusOneModel.md) | A minimal integral Weierstrass equation for the original pointed genus-one curve, with its pointed generic comparison and integral proper flat total scheme. |
| [FunctionField](FunctionField.lean) | Generic-stalk/affine-fraction-field equivalence with the actual x and y maps. Integrality is explicit. |
| [GeometryInputs](GeometryInputs.lean) | Stable exact interfaces for nonsingular geometry and arbitrary pointed-projective j-invariance. |
| [Geometry](Geometry.md) | Over every field, nonzero discriminant gives the actual smooth proper genus-one curve; geometric integrality and constants hold for every equation. |
| [Normality](Normality.md) | Over a domain DVR, nonzero generic discriminant gives normal stalks of the same literal projective cubic, including singular residue fibres. |
| [Genus](Genus.md) | Actual structural-field H¹ is linearly isomorphic to the field, including singular cubics. |
| [Genus/Charts](Genus/Charts.md) | Monic chart bases, actual overlap restrictions and the one-dimensional Laurent quotient. |
| [PoleBasis](PoleBasis.md) | Intrinsic principal-ideal colength forces triangular coordinates for every affine algebra isomorphism over a field. |
| [PointedIsomorphism](PointedIsomorphism.md) | Every origin-preserving isomorphism of the literal nonsingular cubics preserves j, over every field. |
| [PointedVariableChange](PointedVariableChange.md) | Every specified pointed isomorphism of literal cubics over any field is the canonical projective map of a native admissible change, without a discriminant hypothesis. |
| [PointedGroup](PointedGroup.lean) | Adapter to the native genus-one group construction, retaining its Picard representability and other explicit prerequisites. |
| [CoordinateGroup](CoordinateGroup.lean) | Stable operation-comparison interfaces and group-homomorphism bundling for a given pointed group law. |
| [GroupCompatibility](GroupCompatibility.md) | The original characteristic-zero coordinate addition comparison for every given pointed group law, including its original-group points over any field extension. |

In `WeierstrassCurve.Presentation`,
`exists_nonsingular_pointed_weierstrassPresentation` retains the original
curve `X`, field and rational section `p`: its over-isomorphism sends that
same section to the literal infinity section of the constructed equation.
The pole-section and affine-complement constructions supply its coordinate
algebra; a group law or Picard representer is not an input.

`WeierstrassCurve.VariableChange.projectiveOverIso W C` realizes the native
change over any commutative ring as `curveOver (C • W) ≅ curveOver W`,
preserving the actual structural map and infinity section.

`WeierstrassCurve.Projective.pointedIso_exists_variableChange_eq` also starts
from an actual `E : curveOver V ≅ curveOver W` preserving the original infinity
sections. It produces `C`, `hC : C • W = V`, and equality of that same `E` with
`variableChangeOverIso W V C hC`, the coefficient cast followed by the native
projective map. The lower affine classification retains the chosen change and
both original coordinate images. This original-map conclusion holds over every
field without a nonzero-discriminant, group-law or perfectness assumption.

`IntegralModel` starts from a specified fraction-field equation. Over a domain
it clears denominators using an actual native change; over a DVR it selects
Mathlib's `IsMinimal` equation. For two native minima with nonzero discriminant,
`minimal_integral_equations_pointed_iso` descends the specified generic change
`C` to `CR` with `CR.baseChange F = C` and `CR • V = V'`, then uses that same
`CR` for the pointed projective isomorphism over the original DVR. The literal
fraction-field comparisons allow independent coefficient universes; the
categorical generic-fibre wrappers retain their same-universe boundary.

For a DVR `R` and its supplied fraction field `K`,
`WeierstrassCurve.GenusOneModel.exists_minimal_pointed_equation` applies the
presentation and native minimum to an original curve and section satisfying
the same presentation hypotheses over `K`. It returns an integral equation
`V`, `V.Δ ≠ 0`, native `IsMinimal R (V.map (algebraMap R K))`, integrality of
the total scheme and properness and flatness of its structure map. The actual
pointed isomorphism from the original `X` to the mapped cubic retains that
same `K` and section; `R` and `K` may have independent universes.
`exists_minimal_pointed_genericFibre` gives the literal categorical generic
pullback and sends the section to the pullback of integral infinity when
`R` and `K` inhabit the same universe.

Minimality here concerns Weierstrass equations; it does not supply a minimal
regular model or regularity of the integral source.

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
