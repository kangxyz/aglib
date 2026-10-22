# Actual ideal frames on blowup charts

Import `Aglib.AlgebraicGeometry.Blowup.IdealFrames`. In
`Scheme.Blowup.IdealFrames`, a specified
`B : BlowupDatum (affineCenter A I)` over any commutative ring retains its
actual inverse-image centre `centreIdeal B`, its inclusion `centreι B`,
and the original saturated affine charts `A[I/a]`.

`chartCentreIdeal_eq` identifies the actual chart inverse-image ideal with
the scalar image of `I`. The original open chart makes the canonical
`chartIdealPullbackMap` an isomorphism. The algebraic `chartIdealEquiv`,
sheafification and this same canonical comparison construct `chartFrame`.
`chartFrame_inclusion` identifies its composite with the actual pulled
kernel inclusion with multiplication by the original denominator `a`.
`imageIdealIso` separately compares a closed immersion with its native
image inclusion, preserving the original ideal-inclusion map.

`affineMultiplication_pullback` transports multiplication by `s` along an
actual affine ring map `φ` to multiplication by `φ s`, through the native
`pullbackUnitIso`. Thus `chartFrameAfterMap` retains the original frame
and denominator equation for any specified chart-ring map.
`chartFrameAfterMap_transition` takes two such chart maps whose composites
into the same blowup agree, an open-immersion instance for that common map,
and the original denominator relation `t = r * s`. It identifies the
original frame transition with multiplication by `r`, through the native
`pullbackCongr` for that same map equality.

The monomorphic ideal inclusion is cancelled on the actual open overlap,
before any closed-fibre reduction. Only the ideal comparison along the
open chart is inverted; the full pullback of the base ideal along blowdown
is not identified with its image ideal.

[Pullback coherence](IdealFrames/Transition.md) retains these frame maps
through further pullbacks. The current
[regular-point frames](RegularPoint/Normal/Frames.md) use them on the
original reciprocal charts. The
[local normal-line theorem](RegularPoint/Normal.md) then identifies the
actual conormal and normal with `O(1)` and `O(-1)` under its native
regular-local dimension-two hypotheses; the ideal frames alone do not
supply a projective-twist comparison.
