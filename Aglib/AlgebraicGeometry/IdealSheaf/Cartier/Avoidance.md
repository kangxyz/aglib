# Integral avoidance and the canonical ideal map

`Avoidance.lean` proves the original `Cartier.IntegralAvoidanceCartierPullback`
family and a pointwise theorem for any displayed pullback square of a closed
immersion. The target ideal is the actual kernel module. The comparison is
`Scheme.Hom.idealPullbackMap`, defined by the original kernel map and adjunction.

The hypotheses are local rank one of the original ideal module, integrality of
the source of base change, and noncontainment of its image in the closed divisor.
No flatness, Noetherianity, or dimension hypothesis is added.

On a nonempty affine source chart, the pulled-back ideal cannot be zero: its
vanishing would put a dense open inside the closed inverse image of the divisor.
The pulled-back local principal generator is consequently nonzero in a domain.
The regular-principal kernel comparison proves the canonical affine map is an
isomorphism; the existing open restriction and spectral comparisons descend
this conclusion to the original map.
