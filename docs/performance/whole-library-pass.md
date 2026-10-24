> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#whole-library-pass) · [Context](original-context.md) · [Case index](README.md) · [Previous record](recorded-follow-up-measurements.md) · [Next record](equation-proofs-presentations-and-structure-fields.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Whole-library pass

The first aggregate pass covers all 1112 production modules and the requested
positive-test closure, 1136 modules in total, at `55b439b` with the retained
Tensor/Span changes. The ordinary rehashed build passes in 833.99 seconds with
6.17 GiB peak process-group RSS. It records 120 timed compilations and reuses or
restores the remaining artifacts. This is an incremental/cache-restoring build,
not a cold whole-library timing. The source/configuration snapshot remains fixed
through the run.

The historical command at that source revision was:

```sh
AGLIB_BUILD_THREADS=1 python3 scripts/build_serial.py \
  --receipt-dir /absolute/fresh/aggregate --rehash Aglib AglibTest AglibTest.AuditSupport
```

`AglibTest.AuditSupport` and that orchestration have since been retired. Current
production final checks use the native commands in [the local guide](../DEVELOPMENT.md);
the historical timing is not a measurement of that command sequence.

Its slowest actual compilations are `Godement.Section.Localization` (78 s),
`BaseChange.CechComparison` (72 s), `Exact.LongExact` (57 s),
`Duality.Projective.TwistExt.Linear` (39 s),
`Affine.FirstCohomologyPushforward` (38 s), `Duality.Projective.Higher` (35 s)
and `Exact.Euler` (29 s). Cached modules have no new compilation timing in this
pass; their cost remains unknown here.

The [committed-source CI run](https://github.com/kangxyz/aglib/actions/runs/38864750301)
at the same base revision supplies 493 successful production-module timings,
with 619 modules lacking a successful timing row. It fails in
`Cohomology.Restriction.Cartesian.moduleHPrimeOpenMap_pullback_restrict` with
kernel excessive memory consumption after a 190-second module task. That
runner uses four compiler threads, a 12800 MiB native heap limit and a
13824 MiB process-group RSS limit. This resource-profile failure motivates
the Cartesian refactor below.

| Earlier committed CI priority | Successful task s | Transitive reverse imports |
| --- | ---: | ---: |
| `BaseChange.Modules.Map.Open` | 209 | 41 |
| `Restriction.Open` | 141 | 44 |
| `MayerVietoris.Scalars` | 131 | 44 |
| `Modules.Scalars` | 123 | 176 |
| `Modules.Scalars.Open` | 120 | 59 |
| `Cech.Comparison` | 101 | 151 |

These CI observations select the next isolated comparisons; they do not measure
local improvements or complete cold-build time. Broader refactors must preserve
the original scalar actions, base-change mates and component reductions, then
check their actual affected consumers and fill the integration coverage gaps
using matching retained evidence and narrow new checks.

The Cartesian proof now proves the top-open pasting law over abstract coefficient
modules before supplying the original pullback/restriction units. The public
statement is byte-identical, and the former local 500000-heartbeat allowance is
removed. In isolated ordinary compilation with observed native `-j4 -M12800`
and the 13824 MiB process-group bound, the original source exits with a memory
exception after 133.40 seconds, peaking at 13.15 GiB group RSS. The refactor
passes in 71.55 seconds at 7.45 GiB with the default 200000-heartbeat budget.
This establishes bounded compilation success; the failed baseline does not
provide a successful timing ratio. This isolated comparison does not establish
consumer or aggregate integration;
the later native CI-route checkpoint below supplies the recorded integration
coverage.

Two module-sheaf proofs also return to the default heartbeat budget. Global
transport of free generating sections replaces the per-open construction in
`Modules.BaseChange.Basic.unit_isLocallyFree`; abstract sectionwise formulas
replace specialized unfolding in
`Modules.Pullback.OpenRestriction.restrictedPushforwardMap_app`.
Their former 800000 and 400000 allowances are removed. Matched ordinary source
compilations with native `-j1 -M24576` fall from 19.67 to 13.53 seconds and from
22.50 to 20.27 seconds, respectively. The rehashed producer/consumer build passes,
rebuilding the restriction/tensor consumers; the affine mate remains current
under Lake's dependency checks. Public statements and actual map definitions
are retained.

The scalar pass also checks linear-equivalence records over abstract additive
carriers with the exact original module structures. The retained degree-zero
constructor in `Modules.Scalars` preserves its canonical additive equivalence;
its Cech degree-zero and forgetful consumers pass. A refreshed ordinary caller
control has overlapping CPU measurements, so it does not establish a persistent
caller regression or a separate caller speedup.

In `MayerVietoris.Scalars`, the same boundary handles the whole-space linear
equivalence. A second local constructor checks the biproduct comparison over
abstract module-valued presheaves and their actual connecting map before
specializing them. Matched ordinary source compilations with native
`-j1 -M24576` fall from 90.99 to 74.76 seconds, with user CPU time falling from
87.48 to 67.52 seconds. The exactness proof is already below the diagnostic
100 ms display threshold and is unchanged. The real producer, degree-zero
consumer and `Restriction.Top` dependency graph compile; external `rfl` checks
retain the original top equivalence, connecting map and biproduct components.

A proposed abstract factory for `Modules.Scalars.Open` is rejected. Although
its own ordinary user CPU time falls by about 9.94 seconds, the unchanged
Mayer–Vietoris caller gains about 10.22 seconds on the corresponding dependency
basis. This does not establish a library-wide saving. The original open
presheaf definition is retained. Constructor abstraction must be measured at
its actual consumers as well as at the producer.

A subsequent `Restriction.Open` linear-equivalence constructor is retained.
Matched ordinary CI4 source compilations fall from
96.23 to 69.99 seconds, with user CPU falling from 103.47 to 76.08 seconds and
group RSS from 5.10 to 4.87 GiB. The unchanged geometric caller takes 18.87 and
18.73 seconds, respectively; its CPU changes from 21.08 to 20.78 seconds.
Literal forward/inverse component checks and the actual inverse/tensor consumers
`DirectImage.Affine.Localization.Open` and `BaseChange.Modules.Qcqs.Open` pass.
That consumer build recompiles 39 Aglib modules with 8.30 GiB peak group RSS.

`BaseChange.Modules.Map.Open` constructs its natural transformation over
abstract module-valued functors and only then supplies the original geometric
map and scalar-linearity proof. Matched ordinary CI4 producer checks fall from
156.38 to 61.16 seconds, with user CPU from 163.26 to 65.99 seconds and peak
group RSS from 6.84 to 4.30 GiB. The unchanged Mayer--Vietoris caller rises from
34.70 to 42.88 seconds, with user CPU from 36.76 to 43.78 seconds. The combined
producer/caller CPU falls from 200.02 to 109.77 seconds; this pair does not
establish a whole-library improvement.

Literal component, forgotten additive-map and tensor-mate checks pass. The
broader actual-consumer graph also passes, including gluing, open restriction,
localization and the assembled quasicoherent comparison. In matched native
artifact-producing builds, the summed rounded task times of seven common
producer/consumer leaves fall from 373.3 to 341.1 seconds. Several callers slow
down, so the producer saving must not be presented as the library saving.
A separate unit-proof helper regresses the producer to 201.39 seconds and is
rejected; the retained change is the constructor alone.

The finite-support degree-zero formula now proves the cohomology/biproduct
projection law before supplying the concrete stalk-skyscraper maps. Its public
type and all existing definitions and component data are unchanged. The former
800000-heartbeat allowance is removed. Matched ordinary CI4 source checks take
108.12 and 100.46 seconds, with user CPU 102.54 and 98.12 seconds. Peak group
RSS rises from 2.85 to 3.09 GiB, a roughly 245 MiB tradeoff. The production
default-budget build and actual `Exact.Euler` consumer pass, rebuilding
`Support.Finite`, `Exact.Modules`, `Exact.LongExact` and `Exact.Euler`.

The [published first-batch CI](https://github.com/kangxyz/aglib/actions/runs/38922128757)
at `197ca072` completes the 5024-job production/positive-test build and
`lake test`. Fresh task rows include Cartesian at 119 seconds, Span at 190
seconds and Tensor at 31 seconds. This build reuses caches; only 285 production
modules have fresh timing rows, and OpenBaseChange has none. Logged CI bounds
are four compiler threads, a 12800 MiB native heap and 13824 MiB group RSS;
sampled process/RSS receipts are unavailable from that run. Declaration lint
then reports 91 errors across 51 files. Style, axiom, rejection-control,
inventory and independent downstream stages are not reached.

The subsequent source snapshot recorded in
[WORK_PLAN.md](../WORK_PLAN.md#heartbeat-and-compilation-performance-checkpoint)
passes the complete local native
`bash scripts/check.sh --rehash --ci` route with four compiler threads, a
12800 MiB native heap and the 13824 MiB group RSS cutoff. It covers 1159
production modules, 23 trust-test modules and 108 script tests, followed by
production/positive-test builds, declaration/style lint, axiom audits, negative
controls, exact compiled inventory and the independent downstream package.
The production audit covers 15575 declarations; the downstream audit covers
339. The build reuses current native artifacts and supplies no cold-build
speedup measurement. The two additional independent local kernel replays are
not part of this CI route.

The lint repair fills missing documentation, retains historical data names
through five transparent deprecated aliases, and supplies private canonical
simp forms while preserving the public rewrite statements. The derived
pushforward shift instance has one shared owner with the same original data.
Bounded kernel checks pass for 20 original propositions, all five aliases and
four data providers; all 22 registered private simp helpers pass the pinned
simp-normal-form checker. These checks include the subsequent Restriction,
Map and finite-support changes and their actual consumers.

