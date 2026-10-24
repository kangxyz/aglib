# The original dual of the maximal ideal

Let `A` be a commutative Noetherian normal local domain with
`2 ≤ ringKrullDim A`. The native scalar map

```lean
Ideal.scalarToDual (IsLocalRing.maximalIdeal A) :
  A →ₗ[A] (IsLocalRing.maximalIdeal A →ₗ[A] A)
```

sends `a` to the literal map `b ↦ a * (b : A)`.
`IsLocalRing.maximalIdeal_scalarToDual_bijective` proves this map bijective;
`IsLocalRing.maximalIdealDualEquiv` packages the same map as a linear
equivalence. Its forward map is identified by
`maximalIdealDualEquiv_toLinearMap` and `maximalIdealDualEquiv_apply`.

The lower theorem applies to any nonzero ideal contained in no height-one
prime. If `t : I →ₗ[A] A`, linearity gives
`b * t(c) = c * t(b)` for `b,c ∈ I`. Fix nonzero `b ∈ I`. For each
height-one prime choose `c ∈ I` outside that prime. The identity shows local
divisibility of `t(b)` by `b`; the native height-one divisibility theorem
therefore gives `t(b) = b * a` in the original ring. Cancelling `b` gives
`t(c) = a * c` for every `c ∈ I`, with unique scalar `a`.

The maximal ideal is nonzero and avoids height-one primes because its
height is the dimension of the local ring, at least two. There is no
regularity, excellence, completeness, or coefficient-field assumption.

The current geometric consumer is
[`ClosedFibreExtensions`](../../AlgebraicGeometry/Cohomology/Proper/ClosedFibreExtensions.md).
It uses the scalar formula to correct an actual lift in a sheaf extension.
This ring theorem does not produce that geometric lift, prove derived
residue-field vanishing, or construct a resolution of a surface.

The argument uses the native
`HeightOneLocalization → HeightOneIntersection → HeightOneDivisibility`
dependency chain.
