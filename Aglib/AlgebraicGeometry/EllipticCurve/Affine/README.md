# Actual affine Weierstrass coordinates and transport

[Coordinates](Coordinates.lean), in `WeierstrassCurve`, uses literally Mathlib's
`W.toAffine.CoordinateRing`. It supplies the actual X,Y elements, equation,
universal algebra map and uniqueness, together with scale-one translation and
its coefficient formulas. No second coordinate-ring object is introduced.

[CoordinateTransport](CoordinateTransport.lean) specializes the generic
[admissible variable-change maps](../Weierstrass/VariableChange.lean) to scale one
and shear zero. The original forward coordinates X+r,Y+t and inverse
coordinates X-r,Y-t are retained. The same leaf identifies literal coefficient
tensor base change and the original coefficient map, including its etale
property for etale coefficient extension. All base constructions work over
commutative rings; no smoothness, domain, field or Henselian assumption is added.
