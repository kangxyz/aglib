> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#resized-cohomology-diagrams-stop-extensionality-at-the-actual-group-element) · [Context](original-context.md) · [Case index](README.md) · [Previous record](finite-chart-stalk-comparison-use-explicit-native-isomorphisms.md) · [Next record](relative-section-scalars-name-the-actual-transport-before-evaluating.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Resized cohomology diagrams: stop extensionality at the actual group element

FibreProductPresheaf graph132 failed when `ext x` recursively invoked
`Shrink.ext`: the resulting goal had already been transported back into the
original Ext universe, so a subsequent `change` to an equality in the resized
group was not definitionally correct. Its natural-isomorphism proof also left
an unresolved `u + 1 = max w ?v` universe constraint for untyped Shrink maps.
Use `ConcreteCategory.ext_apply` explicitly to stop at the actual resized
group element. Give the source and target Shrink additive equivalences complete
types, and transport the original functor's whole identity equation using
`ConcreteCategory.congr_hom` and `congrArg` instead of implicit rewriting.
Graph135 accepted the full leaf in 219 seconds on 37cce7b, retaining independent
base/slice/scheme Ext universes and the original coefficient sheaves. This is
ordinary compilation evidence, not a speedup claim or evidence that inherited
elaborator transparency options are necessary. No budgets were increased and
no separate benchmark, audit or replay was performed.

