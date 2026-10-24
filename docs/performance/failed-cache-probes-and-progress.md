> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#failed-cache-probes-and-progress) · [Context](original-context.md) · [Case index](README.md) · [Previous record](a-focused-diagnostic-procedure.md) · [Next record](late-lint-repairs-and-dependency-invalidation.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Failed cache probes and progress

In the pinned Lake, `Job.renew` preserves a failure while clearing its action
and log. A dependent job can consequently appear as a green `Ran` entry in a
failed `--no-build` graph. Treat that entry as blocked. Count validated native
output mappings and actual successful builds on the same inputs when reporting
progress. A probe's direct cache misses do not count all pending consumers.
For example, one 791-module probe had 678 valid mappings, 15 direct misses and
98 blocked consumers. Its confirmed progress was 678/791.

