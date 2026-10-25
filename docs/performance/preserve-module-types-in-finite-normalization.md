> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#preserve-module-types-in-finite-normalization) · [Context](original-context.md) · [Case index](README.md) · [Previous record](preserve-regular-equations-through-conormal-comparisons.md) · [Next record](retain-the-original-map-in-ideal-power-comparisons.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Preserve module types in finite normalization

With Lean 4.34.1 and Mathlib `d13f23b`,
`integralClosure.finite_scalar_quotient_of_complete_local_normal_dimLE_two`
in [CompleteLocalSurface](../../Aglib/RingTheory/IntegralClosure/PurelyInseparable/CompleteLocalSurface.lean)
reached the standard 200000-heartbeat limit at `whnf`. Its finite assembly
combined the literal product of local normalization images, the proved
kernel equality and quotient finiteness. Correcting intermediate product
instances alone had not closed this elaboration.

The passing implementation uses the regular named type `surfaceLocalImages`
and its named additive/module structures in both `surfaceToLocalImages` and
`isNoetherian_surfaceLocalImages`. A private regular proposition
`QuotientFinite Q` also appears in both the abstract kernel theorem and
concrete surface producer. The abstract theorem proves it using Mathlib's
`Submodule.CoFG.ker`; a separate abstract adapter matches the scalar
submodule quotient with `QuotSMulTop` once. The final surface endpoint
applies these shared statements. The private boundaries introduce no new
mathematical premise: finite local images, the original coefficient
actions, actual kernel and original hypotheses remain proved and unchanged.

Source `bf29b1f1d43c3e175cac7212d498a4813c01e79550164ea6605daaa80f32c4d8`
failed at `whnf` in native run `remote-ba6b25fe06e741aba407d12e644df10d`.
The complete repaired module, source
`8efdb286d5f297faa28e1191bd6ed57ed0c1cf133448389b8e571a667b851620`,
passed ordinary native compilation in 25 seconds in
`remote-df7e416c5dde4021b771d8c9cdddc29c`, at unchanged default budgets.
The outer graph failed on other modules. This establishes removal of the
tested timeout, not a controlled speedup, unique cause or general compiler
defect. Finite-type Nagata stability and resolution boundedness are separate
mathematical obligations.

The [all-finite-extension wrapper](../../Aglib/RingTheory/IntegralClosure/CompleteSurface.lean)
encountered a related instance boundary at the concrete normal model
`B = integralClosure R F`. Asking for `Module B (integralClosure B M)`
reached the default 20000-heartbeat typeclass limit; manually choosing that
module exposed a parent-structure mismatch in the trace finiteness theorem.
Instead, `finite_of_finite_integral_model` proves the trace/transitivity and
integral-model comparison with `B` an abstract ring parameter. The concrete
consumer receives its conclusion over the original abstract base `R`.
No finiteness premise is added: all normality, fraction-field, finite-model
and separability hypotheses are supplied by the original field construction.

The explicit-module candidate
`138a15eb2b9b0c5bb47898d199b38d448f065f9ebc5f3ee72603ee50bcceb66e`
failed in `remote-68314ede6d02463d9b66ea5eb8be5993`. The abstract-model
version `a5558b461739c12d5958bbbf5d0b2e8afa51cc99e65c43884185d62b5f899e6a`
passed the whole wrapper in 17 seconds in
`remote-a32421a12426431ab6a42af7a2bda5a6`, with all default budgets. These
observations verify the repair on this source; they are not a controlled
comparison of individual instance-search paths or a general speedup claim.

