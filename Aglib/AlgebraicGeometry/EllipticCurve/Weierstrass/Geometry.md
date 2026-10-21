# Geometry of the literal Weierstrass cubic

`Geometry.lean` concerns the existing homogeneous-quotient `Proj`, its
`structureMap W`, and `curveOver W`. The projective equation is the original
one with the term `a₄XZ²`. The coefficient field is arbitrary, including
characteristics two and three.

`affineJacobian_notMem_or` shows that a prime in the actual affine coordinate
ring cannot contain both gradients when `W.Δ ≠ 0`. It maps the coordinate
equation to the quotient domain and applies Mathlib's discriminant criterion
there. Injectivity of the coefficient field map preserves the nonzero
discriminant. No rationality condition on the prime is imposed.

`nonsingularSmoothCover` combines the two existing affine Jacobian
localizations with the existing smooth infinity neighborhood. These cover
every point of the original cubic. Their actual structure triangles and
standard smooth presentations give `structureMap_smoothOne`, with relative
dimension one.

`structureMap_geometricallyIntegral` has no discriminant hypothesis. The
existing integrality theorem applies to the coefficient cubic over every
extension field, and `coefficientBaseChangeIso` identifies it with the actual
categorical pullback. The theorem handles every field-valued base map and
every displayed pullback square. `structureMap_geometricallyConnected`
follows from those actual integral pullbacks.

`curveOver_properties W hΔ` combines relative smoothness, the existing
properness theorem and geometric connectedness. It has exactly the field
and nonzero-discriminant hypotheses. `curveOver_constants_bijective` uses
native proper geometrically integral constants and has no discriminant
hypothesis: its map is the canonical structural map into global sections.

[Genus](Genus.md) computes the original structural-field H¹ of this same
cubic. `nonsingularWeierstrassGeometry` combines the native pointwise
properties with that computation to inhabit the exact original
`NonsingularWeierstrassGeometry` proposition from `GeometryInputs.lean`,
with all its fields and original quantifiers.
[GroupCompatibility](GroupCompatibility.md) supplies the retained operation
comparisons, and [PointedIsomorphism](PointedIsomorphism.md) supplies the
all-fields pointed j-invariance family. Picard representability remains
an external prerequisite of the separate group-law construction.
