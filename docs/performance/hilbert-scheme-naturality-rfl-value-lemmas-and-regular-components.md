> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#hilbert-scheme-naturality-rfl-value-lemmas-and-regular-components) · [Context](original-context.md) · [Case index](README.md) · [Previous record](ringed-coefficient-equivalence-typed-adjunction-unit-boundary.md) · [Next record](picard-pullback-parameterize-the-target-unit-before-specializing.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Hilbert-scheme naturality: rfl value lemmas and regular components

On 2026-10-19 the naturality proofs for the Grassmannian point of a Hilbert family
(`HilbertScheme/Naturality.lean`) were profiled in scratch copies of that leaf with
`set_option profiler true` and `profiler.threshold` 400 ms (200 ms for the last measurement).
The profiler outputs were not retained. The measured kernel times:

1. Rewriting with the composite equivalence, `rw [unitTwistH0Equiv]` followed by
   `simp only [LinearEquiv.trans_apply]`, cost 11.9 s. The `rfl` value lemma
   `unitTwistH0Equiv_apply`, used through `congrArg … |>.trans`, cost 0.24 s. The cause of the
   first cost was not diagnosed.
2. The naturality theorem instantiated at concrete bases cost 7.9 s. Proved once through an
   `rfl` lemma at a variable base `B` and used twice, it cost 3.2 s. From these two numbers,
   unfolding `grassmannianFunctorPoint` costs about 3.5 s per occurrence; this figure is derived,
   not measured directly.
3. Checking the `naturality` field of the natural transformation inline against
   `grassmannianFunctorPoint` cost 14 to 15 s, both through the `algSpec` presentation and with a
   directly defined functor, so the presentation made no difference. With the component as a
   regular definition and its naturality as a lemma stated through that definition, the check
   fell below the 0.2 s threshold.

Candidate mechanism for facts 2 and 3: lazy delta reduction unfolds the higher-height
`grassmannianFunctorPoint` first. This is the case "A structure field compared through its
unfolded statement" above, and the method "Preserve useful regular definition boundaries".

State the values of composite equivalences as `rfl` lemmas at variable arguments and use them
through `congrArg` and `trans`. Give the components of a natural transformation regular
definitions, and prove naturality as separate lemmas stated through them.


