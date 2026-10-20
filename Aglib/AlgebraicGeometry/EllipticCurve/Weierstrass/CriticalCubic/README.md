# Split critical cubics

The namespace `WeierstrassCurve.CriticalCubic` uses the literal Weierstrass
curve `equation k a b` with coefficients `(a,b,0,0,0)`.
`AffineNormalization` constructs its original coordinate map
`X ↦ T²+aT−b`, `Y ↦ T(T²+aT−b)` on the native affine coordinate ring.
The map delegates to the native affine lift; `coordinateMap_eq_liftAlgHom`
is a definitional equality with the source AdjoinRoot map. Degree parity proves
that the same map is injective.

`AffinePinching` assumes two distinct actual roots `r,s : k` of `T²+aT−b`.
These are the entire coefficient hypotheses: no algebraic closure,
characteristic restriction, or replacement model is supplied. The exact image
is the equal-evaluation algebra at `r,s`. The explicit parameter substitution
`t = r + (s-r)u`, with inverse `u = (t-r)/(s-r)`, gives
`coordinateNodeEquiv` to `Polynomial.PinchedPair.nodeRing k`.
Its formulas on both coordinate functions and its normalization, scalar, and
origin triangles are public.

`InfinityRing` identifies the actual homogeneous chart away from `Y-rX` with
`k[w,(w-1)⁻¹]`, using the reciprocal parameter `w=(s-r)X/(Y-rX)`.
`InfinityCharts` proves the full conductor overlap, the inverse-image equations,
and the cover of the same homogeneous Proj. `ProjectivePinching` descends those
specific maps to `pinchedIsoCritical`. Its forward arrow is the displayed
pushout descent. The normalization and both branch triangles, infinity section,
and original-field structure map are preserved.

The prerequisite extraction from `PointedResolution.CriticalCubic.Affine`
contains only the declarations consumed here. Unused finite/fraction-field
normalization utilities and the later projective pointed-resolution assembly
remain with their downstream source owner. No general resolution theorem,
Picard representability, or arithmetic classification is asserted.
