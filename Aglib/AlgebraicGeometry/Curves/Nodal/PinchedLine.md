# Pinching two points of a line

`Affine`, `Gluing`, and `Projective` construct the integral proper curve obtained by
identifying zero and one on the affine line and adjoining the reciprocal infinity
chart. The affine ring is the literal subalgebra
`Polynomial.PinchedPair.nodeRing k = {p : k[X] | p.eval 0 = p.eval 1}`.
The polynomial algebra, conductor localizations, cubic presentation, and
one-dimensional normalization defect live in
`Aglib.RingTheory.Polynomial.PinchedPair`.

The scheme namespace is `AlgebraicGeometry.Scheme.PinchedLine`. Its
`normalizationMap` is exactly `Spec.map` of the subalgebra inclusion.
`gluedNormalizationMap` is the open-pushout descent of that map and the identity
infinity chart. It is finite and surjective. The complete spectrum fibre above
`gluedNodePoint` consists of the two distinct `gluedBranchPoint`s, in every
characteristic. The canonical `ProjectiveComparison.lineIsoP1` identifies the
normalization gluing with the existing native `Scheme.ProjectiveLine.projectiveP1`.
The pinched curve is proper, integral, and nonnormal.

`CriticalPoint` uses the shared `WeierstrassCurve.translate` on the same
Weierstrass equation. Over a Henselian local ring, an actual residue critical
point with nonzero Hessian has a critical lift; no perfectness or residue
characteristic condition is added. At a critical origin, unit `b₂` and nonunit
`a₆` give equality of the normalized discriminant and `a₆` valuations over a DVR.

`SplitChart` uses `WeierstrassCurve.Affine.TangentNode` to construct the common
étale neighborhood of the literal affine cubic and `PlaneNode.Ring W.a₆`.
The maps, residue point, and structure triangles are explicit. The original
`a₃ = a₄ = 0`, tangent root, and simple-root hypotheses are retained.
`CoordinateTransport` is the separately migrated and frozen transport provider;
its source is `LocalModels.PointedResolution.Nodal.CoordinateTransport`.

The explicit critical-cubic identification is in
`EllipticCurve.Weierstrass.CriticalCubic`; actual P¹ pair normalization is in
`ProjectiveSpace.Line.TwoPoints`. No pointed-resolution assembly or arithmetic
marking is part of these leaves.
