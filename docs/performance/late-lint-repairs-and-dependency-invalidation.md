> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#late-lint-repairs-and-dependency-invalidation) · [Context](original-context.md) · [Case index](README.md) · [Previous record](failed-cache-probes-and-progress.md) · [Next record](placement-edits-in-widely-imported-modules.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Late lint repairs and dependency invalidation

The relative duality integration's final lint repair added missing docstrings,
adjusted declaration attributes and reused the existing derived-pushforward
shift instance. The surviving theorem, proof and map bodies were preserved,
but the native build inputs changed. Required consumers were invalidated:
`Relative.Trace.Core` took 350 seconds and `Canonical.ModelCharts.Principal`
took 429 seconds in the repaired-source check. This was renewed checking of
changed inputs, rather than a new mathematical gap.

Include docstrings with new declarations, settle final lint repairs together,
and preserve compiled outputs so native cache matching can reuse unaffected
consumers. Assign parallel builds disjoint pending dependency chains: two full
targets can repeat a shared in-flight prerequisite before its cache entry exists.
The integration initially repeated `Relative.AffineTrace` in two full target
graphs. It then restricted the second worker to the missing canonical
`ModelCharts.Principal` branch while the trace/comparison graph continued.

