> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#hilbert-scheme-direct-images-compare-isomorphism-values-at-the-iso-level) · [Context](original-context.md) · [Case index](README.md) · [Previous record](name-local-instances-in-independently-imported-public-modules.md) · [Next record](picard-tangent-space-prove-additive-group-algebra-abstractly-then-specialize.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Hilbert-scheme direct images: compare isomorphism values at the `Iso` level

On 2026-10-24 `HilbertScheme/DirectImageSheafQuotient.lean` took 188 s
(remote-5a89d2ea0cc24fbc8f2dd4abc43927c9). Kernel type checking of two instance lemmas dominated
(profile remote-34601a9d7fc74950b0c7fb714406c522, threshold 500 ms):
`pullbackFreeMap_familyQuotientMonomialMap_pointMap` took 123 s and
`pullbackFreeMap_familyQuotientMonomialMap_baseChangeMap` 47.7 s. The general lemma they
instantiate, at a variable morphism `p`, took 1.7 s. Their statements use the regular definitions
`familyQuotientTwistPointIso` and `familyQuotientTwistBaseChangeIso`, and their proofs reached the
unfolded isomorphisms, by `rw` or by direct application.

Two remedies did not help: proving the instances by plain application of variable-argument lemmas
(92 s and 36 s), and unifying the two presentations of the tensor product,
`moduleTensorLeftFunctor` against the monoidal `⊗` (126 s and 46 s). Probes at threshold 100 ms
(remote-c8b57012a9c94a228657ca6a3daca159) isolated the conversion: the equation
`familyQuotientTwistBaseChangeIso … = <value> := rfl` checked in under 0.1 s, and so did the
instance stated with the value; the instance stated with the definition took 45 s.

The repair adds named `rfl` value lemmas at variable arguments (`familyQuotientTwistBaseChangeIso_eq`,
`familyQuotientTwistPointIso_eq`, `familyQuotientMonomialMap_eq`) and proves each instance as
`(congrArg (fun i => _ ≫ i.hom) _eq).trans lemma`. The module then built in 24 s under the
profiler, with cumulative kernel time 7.5 s (remote-3bb84110e86249bc9fdb4c5acdf7610d), and in 18 s
without it (remote-29575aba19604befa46fa4e8c33bd36f). Default budgets were kept; no statement
changed.

Candidate mechanism, not checked against a kernel trace: comparing `(d …).hom` with the `.hom` of
`d`'s value reduces the projection, which forces weak-head normalization of the isomorphism
structures before `d` is unfolded; at the `Iso` level, lazy delta unfolds `d` first.

When an equation's statement uses a definition of an isomorphism or morphism and its proof produces
the value, bridge them with a named `rfl` lemma through `congrArg` and `trans`, not by `rw`, `exact`
or a type-changing application. This is the method of "Hilbert-scheme naturality: rfl value lemmas
and regular components" applied to isomorphism values.

