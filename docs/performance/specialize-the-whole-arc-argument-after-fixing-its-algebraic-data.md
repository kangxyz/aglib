> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#specialize-the-whole-arc-argument-after-fixing-its-algebraic-data) · [Context](original-context.md) · [Case index](README.md) · [Previous record](keep-the-completed-stalk-equation-through-specialization.md) · [Next record](cache-independent-chart-producers-before-concrete-geometry.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Specialize the whole arc argument after fixing its algebraic data

The equal-count step in
[ArcTermination/Descent](../../Aglib/RingTheory/Blowup/ArcTermination/Descent.lean)
repeatedly exhausted the default 200000-heartbeat `whnf` budget when its
minimality and transformed-kernel equations were specialized to the actual
localized arc ring. Merely naming the target ring, or sharing a kernel-span
proposition while still specializing intermediate calculations separately,
was insufficient. Native run `remote-c0a48689d3a74b3c9f52479f5fb84e97`
records the remaining failure in the equal-count step.

Move the entire algebraic argument into one generic producer with a fixed
target ring, quotient map, localization structure and uniformizer. Keep
`KernelSpanEq` as the exact original kernel/span equation in both the
localization producer and the minimality/realization consumer. The actual
instance is proved from the original chart and quotient composite; it is
not an extra hypothesis about the arc. Specialize once, supplying those
same native structures explicitly. Preserve the original raw power
relation when extracting its exponent and unit, rather than confusing it
with the outer relation object.

Exact Descent source
`6eca82a1c83ba6d2e874b83f65b6cf2df416c94dda543be4cde8ffc4550012f2`
passed the whole module in 80 seconds in
`remote-ad1455766c90484085f7debe96f7ff67`, source snapshot
`847a187c5e3a40fb5026465ad82e7c6d47327c402767558d265858037e6eae15`.
The pinned toolchain and default budgets were unchanged. This covers the
actual strict measure, finite local-ring iteration, original scalar and
quotient equations, and the regular-generic DVR supplier. It does not
cover the subsequent comparison with original scheme point blowups or
full surface resolution. Other proof repairs accompanied the structural
change, so no controlled speedup ratio or profiled compiler cause follows.

