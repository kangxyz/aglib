# Pure degree-p field differential transpose

The original finite purely inseparable extension L/K of prime degree p in
characteristic p receives a presentation `L = K[z]/(z^p-a)` through its
original coefficient map. A root outside K generates L by prime degree;
its pth power belongs to K, and the shared lower
`IsAdjoinRootMonic.ofPowerRelation` constructs `IsAdjoinRootMonic`. Its map is literally `Polynomial.aeval z`,
its root is z, and its native power basis has entries `z^i`.

`mapExterior_tower` and `mapExterior_self` extend the wedge formulas to the
whole original exterior modules. They supply the actual map equations used
by coordinate independence and the integral-normalization trace.

`LinearMap.smulTranspose` curries original scalar multiplication followed by
an original linear map. It assigns no upper-ring action to the target. The
field and integral-normalization transposes are its two consumers.

`pureDegreePFieldTranspose` transposes the actual differential trace. For
β = image(η) wedge dz and q = η wedge da, its original power-basis formula is

```text
T(z^j z^i β) = q     if i+j=p-1,
T(z^j z^i β) = 0     otherwise, for 0 ≤ i,j < p.
```

When i+j≥p, the original relation z^p=a reduces to a killed lower exponent.
This proves the antidiagonal pairing, including characteristic 2.

`pureDegreePFieldTranspose_bijective` assumes the actual source and target
exterior powers are generic lines and q≠0 over K. Its normalized trace
proves β≠0. Writing an arbitrary source as cβ and evaluating at
z^(p-1)c^(-1) proves injectivity; the actual K-dimensions agree. No integral
wedge or coefficient in A is required to be a unit generator. These line
and nonzero-wedge conditions are genuine generic differential data.

The trace is independent of the original root presentation. No ordinary
inseparable field-trace functional, perfect field, finite p-rank, invertible
factorial, residue separability, or trace-compatibility premise is used.

`pureDegreePFieldTranspose_dual_root_powers` reverses the form exponents:
T(z^j · z^(p−1−i)η_L∧dz) = δ_ij η∧da for 0≤i,j<p. It follows from the
antidiagonal formula including the reduction of exponents at least p, so the
normalization has no unspecified nonzero scalar factor.

The generic pairing proof is isolated as
`LinearMap.smulTranspose_bijective_of_lines`. For an actual finite extension
L/K, a one-dimensional L-space W, a one-dimensional K-space V, and a
K-linear map t : W → V with t(cβ) nonzero for specified c∈L and β∈W,
it proves bijectivity of w ↦ (b ↦ t(bw)). A nonzero w=dβ can be rescaled
by cd⁻¹ to recover the fixed nonzero trace value, proving injectivity;
restriction-of-scalars dimensions give surjectivity. The differential
specialization supplies t and its normalized root-power equation, without
an additional pairing hypothesis. This abstraction keeps the same maps
while avoiding repeated expansion of concrete exterior presentations.

The power-relation constructor is shared with the actual DVR and integral-
generator presentations. This field leaf no longer has its own minpoly/degree
comparison body; its original existential statement, root, map and coefficient
choices are unchanged. This exact thin caller passed its native own-node
check in graph66 on 2026-10-31 (0e96f20a, 6.0 s), under normal caps. The
containing graph later hit an unrelated aggregate RSS guard; no whole-graph
completion is claimed.
