# Original frames of the regular-point blowup

This owner uses the actual `blowupDatum (affineCenter A I)`, its original inverse-image
centre and the kernel of its actual inclusion. The original Cartier proof supplies
`centreIdealLine`. Its restriction and the restriction of its dual give
`centreConormalLine` and `centreNormalLine`. The latter is the precise module used by
`actualSelfIntersection`; no normal-line family is supplied as an input.

For a commutative ring A, an ideal `I = span {a,b}`, a regular on A, and b regular modulo a,
the actual saturated blowup chart supplies the original denominator frame. Pullback to
the actual polynomial quotient-fibre chart retains the original inclusion and structural
triangles. For the overlap calculation, b is also regular on A and a regular modulo b.
The actual reciprocal chart maps agree and retain the equation b = (b/a)a.

`rawOverlapFrameComparison` is identified, both as a whole isomorphism and by its forward
component, with the literal native `pullbackCongr` for that proved chart-map equality.
`rawOverlapFrameComparison_inclusion` retains the original pulled kernel inclusions.
Their monomorphism property is used on the original open overlap before fibre reduction,
so the original denominator equations give `rawOverlapFrames_hom`.
`laurentOverlapFrames_hom` pulls this equality through the original Laurent reduction,
sending the coefficient to the literal T(1). `conormalLaurentFrames_transition` retains
the two actual centre chart maps and their native comparison. Only isomorphisms are
cancelled after fibre reduction.

The generic comparison constructor has a full checked opaque body. Its plain isomorphism
and equations are projected while schemes remain symbolic, then specialized to the actual
blowup. This controls dependent conversion cost without changing a map, adding an axiom,
or assuming an equality or compatibility family.

For a regular local ring of dimension two, the chosen parameters and centre charts are
exactly those in the frozen `RegularPoint` owner. There is no excellence, Henselian,
completeness, perfect-residue-field or characteristic condition. The original
conormal/restricted-dual evaluation and every forward frame equation are retained.

The actual intrinsic/native projective cocycle comparison belongs to the current consumer
[RegularPoint.Normal](../Normal.lean). This local frame result alone is not the global O(-1)
comparison, a numerical self-intersection, a contraction or a factorization theorem.

The three imports are `RegularPoint`, frozen `IdealFrames.Transition`, and
`Invertible.PullbackTensor.Local`. Exact Lean source
`2677a81f189d5b81153161a453c4e272def7d5bcaa884dc0a99622c0121bd02b` passed its actual native
frontend in 35 seconds at the unchanged default of 200000 heartbeats in Original run
`remote-c14d1672d50d4900a41f25e5de8929b2`. The combined graph failed in other requested
modules, including the first invoked complete Normal consumer. Source and invocation
bindings are retained in the author handback. No extra replay or validation stage was run.
