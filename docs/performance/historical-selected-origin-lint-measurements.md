> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#historical-selected-origin-lint-measurements) · [Context](original-context.md) · [Case index](README.md) · [Previous record](remote-resource-calibration-on-the-unchanged-library.md) · [Next record](binary-form-section-and-geometric-point-typing.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Historical selected-origin lint measurements

Lean 4.34.1's builtin lint driver imports a server-level environment for each
selected module. The pinned Batteries driver also imports an environment per
module. Import regions can remain mapped across these iterations, so a batch
can exceed the memory limit even when each module fits comfortably by itself.

On 2026-10-19, the seven geometric-regularity providers compiled successfully,
but one builtin-lint invocation over all seven was stopped at an observed
14,527,889,408 bytes RSS under the 13,824 MiB process-group cutoff. A fresh
process checking the final criterion, whose imports include all seven providers,
passed at 2,876,129,280 bytes. Separate builtin invocations for all seven passed
with a maximum of 2,867,855,360 bytes (about 2.67 GiB).

The historical selected-checker and exact-origin declaration wrappers ran
separate processes for selected origins. Those wrappers and AuditSupport have
since been retired. Current local final checks use native production lint and
the pinned upstream production axiom auditor, retaining compatible successes;
they do not run another per-origin acceptance chain. Reuse successful provider
compilation after a lint failure and check only changed or missing coverage.
Historical per-origin and current production results retain their distinct input
and predicate bases; this migration does not itself measure a speedup.

