> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#additive-ext-transport-avoid-an-irrelevant-integer-module-diamond) · [Context](original-context.md) · [Case index](README.md) · [Previous record](short-complex-colimit-comparisons-normalize-abstract-endpoints-first.md) · [Next record](pullback-gamma-coherence-transport-typed-identities-explicitly.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Additive Ext transport: avoid an irrelevant integer-module diamond

Graph073 of ExactImageComparison.Cohomology, with pinned Lean4.34.1 and
Mathlib d13f23b, failed when converting `Ext.precompLinearEquiv ℤ` to an
additive equivalence: the inferred integer module on the native Ext carrier
was not definitionally equal to `AddCommGroup.toIntModule`. This scalar
structure is irrelevant to the additive cohomology endpoint and is not a
missing Ext-size instance.

Use the scalar-free `Ext.precompIsoAddEquiv`, built from original `Ext.precomp`
and the actual isomorphism and its inverse, with native Ext associativity.
Retain original `Adjunction.extEquiv`, cohomology pullback/counit and independent
source/target HasExt universes. Explicit associativity degrees0,q,0,q avoid
unresolved degree metavariables. Existing graph076 then accepted the complete
Cohomology leaf in60 seconds; Exact graph071 and Exchange graph073 were
unchanged. No additional benchmark, replay or budget change was used.

