# Actual exceptional conormal and normal lines

This file identifies the actual exceptional conormal and normal lines of the same blowup
constructed in `Blowup.Construction`. The conormal is the restriction of the actual
inverse-image-centre kernel ideal. The normal is the restriction of its dual, exactly the
object used by `actualSelfIntersection`. The original parameter choices, quotient maps,
chart triangles and centre-over-P1 isomorphism are retained.

The assumptions are `[CommRing A] [IsRegularLocalRing A]` and
`hd : ringKrullDim A = 2`. For this native regular local ring, the endpoint adds no
excellence, Henselian, completeness, perfect-residue-field or characteristic hypothesis.

`centreConormalTwistingIso A hd` identifies the pullback of native O(1) with the actual
conormal module. `centreNormalTwistingIso A hd` identifies the actual restricted dual with
the pullback of native O(-1). Both use `nativeCentreComparison A hd`: the SAME
parameter-dependent `centreOverIsoProjectiveP1 A hd`, followed by the canonical
`ProjectiveSpace.finUliftIso`. `centreNormalProjectiveP1Iso A hd` states the result directly
through the literal polynomial projective line and that canonical coordinate lift.

## Original maps and proof

The two indexed charts and frames are finite eliminations of the original parameter
charts and whole frame isomorphisms, with explicit zero/one equations. Their actual range
frames construct the intrinsic conormal unit cocycle. Native restriction/pullback coherence
in `Normal.Sections` evaluates its coefficient on the original Laurent overlap. The lower
calculation uses a checked presentation whose body is the literal native kernel pullback
and identity comparison; its proved `conormalOverlapCoefficient_original` equation returns
exactly the coefficient of the original frames used by this cocycle. No comparison family
is assumed, and the original cocycle and generators are unchanged.

The original frame relation is b=(b/a)a, so the conormal transition evaluates to T(1).
The native homogeneous fraction X0/X1 evaluates to T(-1); the inverse transition used by
native O(1) therefore evaluates to T(1). The original Laurent open immersion detects equality
on the whole actual overlap. Genuine unit-cocycle laws give the diagonal and reverse cases.
This proves `conormalCocycle_isPullback` for the actual native projective twist and the actual
intrinsic kernel-frame cocycle.

Native cocycle pullback and reconstruction produce `centreConormalTwistingIso`.
`centreConormalTwistingIso_hom_generator` retains the original pulled generator on every
actual parameter subopen. The actual conormal/restricted-dual evaluation and native
multiplication of positive and negative twists then produce `centreNormalTwistingIso`.
`centreNormalTwistingIso_tensor_hom` preserves the exact original evaluation morphism.
No kernel inclusion is cancelled after reduction to the exceptional fibre; its earlier
cancellation belongs to the original open overlap before reduction.

This is supporting local blowup geometry. It does not establish numerical self-intersection,
contraction, factorization or minimal-model existence. The classical exceptional-line and
normal-bundle statement is [Stacks, Lemma 54.3.1 (0AGQ)](https://stacks.math.columbia.edu/tag/0AGQ).
[Stacks, Lemma 54.3.2 (0AGR)](https://stacks.math.columbia.edu/tag/0AGR) addresses ambient
regularity, whose formalization has a separate owner.

## Native source and coverage

Lean source SHA:
`b4a040ce507ac187cd76a7c991cdbe794caeaedc90a6f5c1cfb7f99fbafe13ac`.
The actual Normal frontend passed in 235 seconds, together with Sections75d (59 seconds),
in Original run `remote-13a19a804a194f31bf75e68c604e5333`, SOURCE
`1375fb371689f028bc72fa2ccf0e8f7fd9dafe42166f7db3ed10ab205fe0020f`.
The combined graph exited 1 solely because an independent PointIdeal target failed.
Both own successful module blocks and the source-bound native receipt are retained; this
is not a claim that the entire mixed graph passed.

Normal and all helpers retain default200000 heartbeats. The matching Sections provider
uses its explicitly authorized local800000 setting only for the concrete coefficient
comparison; its optional helper400000 allowance was never used. No checks were disabled,
no file-wide/zero allowance was introduced, and no replay or separate positive-provider
run was added. Frozen Frames2677 and prior P1/ideal suppliers were reused unchanged.
This guide was finalized after the run without altering the compiled Lean source.
The principal retains the final ordinary mathematical-review and adoption decision.
