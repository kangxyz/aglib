> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#recorded-follow-up-measurements) · [Context](original-context.md) · [Case index](README.md) · [Previous record](what-the-measurements-establish.md) · [Next record](whole-library-pass.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Recorded follow-up measurements

The first follow-up comparison starts from Aglib
`55b439b7219f12ad6ff2645b32d9f8b073dd8b28` and changes only
[Tensor](../../Aglib/AlgebraicGeometry/Cohomology/Godement/Tensor.lean) and
[Span](../../Aglib/AlgebraicGeometry/Cohomology/Godement/Section/Span.lean) in the
measured mathematical source. Tensor proves the whiskered quasi-isomorphism
through a private lemma with abstract functor endpoints. Span uses the local
constructor described above. Their public types, hypotheses and actual component
maps are retained, with the standard 200000-heartbeat budget.

| Module | Baseline guarded wall s | Refactored guarded wall s | Baseline / refactored peak group GiB |
| --- | ---: | ---: | ---: |
| `Godement.Tensor` | 64.21 | 22.07 | 7.70 / 3.29 |
| `Godement.Section.Span` | 226.71 | 122.15 | 12.64 / 6.79 |

Tensor's `godementTensorTotalUnit_quasiIso` kernel task falls from 42.79 seconds
to below the 100 ms display threshold. Span's source-arrow naturality auxiliary
and constructor similarly fall from 82.72 and 24.06 seconds to below that
threshold. Tensor's user CPU time falls from 66.73 to 22.38 seconds. The remaining
displayed Span kernels include `sectionTotalToRepeated_quasiIso` at 32.56 seconds,
`pushforward_godementTotal_map_quasiIso` at 23.11 seconds and
`sectionSourceTotalToRepeated_quasiIso` at 21.64 seconds.

These are successful local source compilations with the same pinned dependencies,
production setup options and launch settings, one guarded frontend, `trace.profiler` at 100 ms,
and isolated `.olean` outputs. They include imports, checking, linting and output
serialization, without C generation. Another Quillen build was active on the
host; these observations are not whole-library or CI speedup measurements.
Nested and asynchronous profiler intervals overlap and must not be added.

These initial comparisons preceded a correction to the direct `lake env lean`
resource wrapper. Lake can prepend its compiler directory to `PATH`, bypassing
a bare wrapper name. The comparisons retain their matched launch conditions,
but they do not certify propagation of explicit native thread/heap flags.
The current guard binds the absolute wrapper; subsequent runs verify actual
`-j` and `-M` arguments separately from parent and process-group limits.

For reproduction on macOS after a focused Lake build, use the module's current
owned
`.lake/build/ir/...setup.json`, a fresh receipt and a separate output path:

```sh
AGLIB_BUILD_THREADS=1 python3 scripts/resource_guard.py --capped-toolchain \
  --receipt /absolute/fresh/profile.json -- \
  /usr/bin/time -lp lake env lean \
  --setup .lake/build/ir/Aglib/AlgebraicGeometry/Cohomology/Godement/Tensor.setup.json \
  -Dtrace.profiler=true -Dtrace.profiler.threshold=100 \
  -o /absolute/fresh/Tensor.olean \
  Aglib/AlgebraicGeometry/Cohomology/Godement/Tensor.lean
```

Compile the changed producers and their actual consumers through the ordinary
focused build route. `ArchiveGodementClosedSectionSpan` checks the original
source-arrow component by `rfl`; `Godement.Section.Units` consumes its original
derived-unit equation. `ArchiveGodementTensor` checks the literal component and
its rewrite-based quasi-isomorphism proof, and `Godement.Contraction` exercises
the tensor interface.

The focused rehashed build passes both producers and all four named consumers.
Units and the archive fixtures were rebuilt against the producer artifacts;
Contraction retains current cached artifacts under Lake's dependency checks.

`OpenBaseChange` remains a separate bottleneck. A full globally instrumented run
of the unchanged source reached the default heartbeat limit in three component
lemmas. That failed profile supplies no successful whole-module baseline and
does not establish failure of an ordinary build. At the merged `197ca072`
snapshot, fresh ordinary source compilation with observed native `-j4 -M12800`
and the 13824 MiB RSS cutoff passes in 338.94 seconds, with 392.83 seconds user
CPU and 9.84 GiB peak group RSS. The retained Span passes in 115.75 seconds with
6.14 GiB peak group RSS under the same bounds. These checks reuse their pinned
imports and write isolated outputs; they are not cold whole-library builds.

A first-square proof-helper candidate for OpenBaseChange passes in 329.76
seconds with 385.66 seconds user CPU and 10.15 GiB peak group RSS. The native
setup and all 2985 import-artifact identities match the baseline. This small
time difference with higher memory does not justify the additional helper;
the original source is retained. A more useful boundary still needs attribution.
The isolated Tensor recheck stops at setup because three import artifacts need
rebuilding; it supplies no additional Tensor source/resource verdict.

A faithful theorem-binder probe for the first-square proposition completes with
4.36 ms cumulative native type checking across its small source; imports take
6.06 seconds. Thus this proposition can be formed cheaply on its own. The probe
does not check the original proof body or attribute the remaining module cost.

