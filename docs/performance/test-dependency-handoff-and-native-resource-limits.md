> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#test-dependency-handoff-and-native-resource-limits) · [Context](original-context.md) · [Case index](README.md) · [Previous record](local-validation-and-shared-artifact-link-metadata.md) · [Next record](whole-module-exchange-comparisons-before-evaluating-components.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Test dependency handoff and native resource limits

A successful root-only `-o` export does not include upstream outputs. If Test's
optional Actions restore misses or fails, public cache acquisition alone cannot
supply an unpublished dependency leaf compiled by Build. Build now transfers
its native `artifacts/` and `outputs/` snapshot separately from the public
production archive. Test restores it only on that cache miss/failure, obtains
pinned Mathlib artifacts and overlays the current root archive last. Streaming
tar through zstd avoids an uncompressed intermediate; no new cache-map format,
production rebuild in Test or checker preparation in Build is introduced.

A bounded Lean 4.34.1 fixture reproduced the gap: the current root archive plus
published seeds failed `--no-build --rehash` on `Aglib.Changed`. Importing the
same Build's dependency snapshot made that unchanged request pass without
compilation. The workflow's 46 regression tests include cold/failed restore
routing, overwriting read-only partial files, executable-mode preservation and
exclusion of the auditor checkout. These are transport results, not a complete
three-library CI pass.

The historical limits are retained through native controls: each maintained
package uses weak `-M12800` arguments, which do not invalidate artifact traces.
The three libraries use Aglib's four-thread frontend setting, `-j4`, and retain
`LEAN_NUM_THREADS=1` for Lake. Older pinned dependencies and the auditor retain
their own arguments.
A systemd scope bounds each run step and its subprocesses at at most 13824 MiB,
reduced for machines with less than that allowance plus a 2048 MiB system/runner
reserve. This cgroup limit covers more than process RSS; no CPU-saturation or
throughput improvement has been measured.
The Actions runner stays outside the scope so ordinary workload failure can
reach the existing cache saves. Runner/VM teardown still cannot guarantee saving,
and the earlier shutdown's cause remains unknown.

[The first hosted run](https://github.com/kangxyz/aglib/actions/runs/40007949025/job/120600585739)
failed before cache acquisition: Ubuntu 24.04's systemd rejected
`MemoryOOMGroup=yes` as an unknown assignment. That unsupported property was
removed; `MemoryMax` and `MemorySwapMax` retain the native resource bound.
Do not infer a guarantee that every process in the scope is killed together.

GitHub's custom shell is launched through .NET argument parsing, which does not
group POSIX single quotes. The shell uses double-quote grouping with escaped
inner quotes, checked against the [runner launcher](https://github.com/actions/runner/blob/v2.338.0/src/Runner.Sdk/ProcessInvoker.cs#L228)
and [.NET parser](https://github.com/dotnet/runtime/blob/v8.0.12/src/libraries/System.Diagnostics.Process/src/System/Diagnostics/Process.Unix.cs#L868-L939).
An actual local .NET launcher preserved script paths with spaces, environment
and exit statuses 0/7 under simulated 16 GiB and 7 GiB RAM. Its systemd boundary
was mocked. The [corrected hosted run](https://github.com/kangxyz/aglib/actions/runs/40008706099/job/120603170297)
then passed its first scoped command and reached Actions cache restoration.
A full pipeline pass and induced-OOM behavior are not established by that step.
This repair adds no kernel replay, client workflow or mathematical acceptance
requirement.

