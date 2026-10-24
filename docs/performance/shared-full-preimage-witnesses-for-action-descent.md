> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#shared-full-preimage-witnesses-for-action-descent) · [Context](original-context.md) · [Case index](README.md) · [Previous record](typed-evaluation-of-coefficient-map-composites.md) · [Next record](augmented-amitsur-differentials-and-typed-tensor-coordinates.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Shared full-preimage witnesses for action descent

For the actual finite-cover action and positive difference maps in
`EtaleCohomology/H1/ConstantFinite/ActionDescent`, specializing
`congrArg (fun k => k.hom) (F.map_preimage ...)` directly at the concrete
coefficient/carrier products exhausted 200000 heartbeats at `whnf` and
`isDefEq` in `remote-aa8b53b3090e4d51949e309f2e1ddfa2`.

Keep the native full preimage and its literal pullback equation together in
one regular constructor with variable covers and variable arrow. The private
`liftedArrow` returns `{r : U.obj ⟶ V.obj // (Over.pullback f).map r = q}`.
Its value is exactly the original native full preimage. Both concrete action
and difference maps use this value, and both pullback formulas use the same
constructor's property. No product comparison or positive-action convention
changes.

The complete ActionDescent provider compiled in 6.4 seconds in
`remote-f8f2cf772a974889897ebdff1dbe8a7b`, source SHA-256
`ad8af195f047f1eb085d20bebf96b07068cd799a08b39510f44ffec899b6fe8f`,
under unchanged heartbeats and resource ceilings. That invocation's final H1
consumer still failed on a separate structural-arrow rewrite; it is not
claimed as H1 completion evidence. The final H1 root subsequently compiled
in `remote-c25304d9e9944faa8eedbd942e570ea8`. This extends the typed-transport
finding using existing proof-iteration observations, without an extra benchmark.

