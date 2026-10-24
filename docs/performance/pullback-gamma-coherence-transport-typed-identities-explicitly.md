> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#pullback-gamma-coherence-transport-typed-identities-explicitly) · [Context](original-context.md) · [Case index](README.md) · [Previous record](additive-ext-transport-avoid-an-irrelevant-integer-module-diamond.md) · [Next record](finite-pointed-lifts-name-the-residue-point-morphism.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Pullback Gamma coherence: transport typed identities explicitly

In Continuity.PullbackCohomologySystem, graphs078–080 could not simplify
identity maps inside inverse-image composite comparisons: composite.obj and
nested.obj left the native `map_id` and `id_comp` endpoints unmatched.
Keep the original comparison isomorphism and transport the typed `map_id`
and `Category.id_comp` equations with `congrArg` through its complete hom
and inv endpoints. Compose those equations using `Eq.trans`, finishing with
original `Iso.hom_inv_id_app`, rather than expanding the composite functor.
Graph082 accepted the complete leaf in40 seconds on the pinned Lean4.34.1
and Mathlib d13f23b baseline. No heartbeat, transparency or synthesis budget
was raised, and no extra benchmark or kernel replay was run.

