# Investigating Lean compilation performance

This guide separates measured Aglib bottlenecks from candidate explanations and
records primary-source methods for investigating them. The compatibility basis
is Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. External issue states were checked on
2026-10-16. Historical reports do not establish a defect in the pinned compiler.
[Caching](CACHING.md) owns artifact reuse; this guide concerns the cost of
checking a declaration when compilation is necessary.

## What the measurements establish

The successful [cold CI run](https://github.com/kangxyz/aglib/actions/runs/38711518878)
at `419bd685cee21ac408756fbfe99565be19d186fd` reported 673 seconds for
`Godement.OpenBaseChange`, 378 for `Godement.Section.Span`, and 225 for
`Godement.Tensor`. The twelve slowest modules accounted for about 52% of
reported library task time. That CI run omitted extra independent kernel replay.
Its build helper admitted one external compiler at a time, so scheduling also
contributed to whole-library wall time.

Local declaration profiling distinguishes a different problem inside these
files: kernel checking dominates tactic execution. For example,
`godementTensorTotalUnit_app` spent about 80 seconds in the kernel despite its
proof being `rfl`. This does not establish large instance-search or simplifier
cost. Profiling categories and asynchronous tasks can overlap; their cumulative
times must not be added or treated as wall-time percentages.

The retained changes use explicit object representations and narrowly typed
proof helpers:

- In the Tensor component, the inferred codomain `F.obj (G.obj C)` is compared
  with the same object represented as `(G ⋙ F).obj C`. Explicitly aligning the
  map's source and composite codomain reduced an isolated module measurement
  from 144.58 to 103.82 seconds under the same setup. An isolated type-formation
  probe fell from 35.18 seconds and 10,936,920 unfolding events to less than a
  millisecond and 36 events. These counters describe that probe, not the whole
  module.
- The subsequent archive integration supplies a typed whiskering-component
  equality through `NatTrans.unitPostcompose_whiskerRight_app_of_eq`, retaining
  that object alignment. In its fresh artifact-producing run, Tensor passed in
  60.66 seconds; its component-app kernel task was below the profiler's 100 ms
  display threshold, compared with 43.28 seconds in the prior aligned candidate.
  This run has different output/profiling settings from the isolated module
  comparison, so the wall times are not a controlled speedup ratio. The original
  component equation and its actual rewrite-based quasi-isomorphism consumer
  both pass. The refactor below addresses the remaining
  total-quasi-isomorphism task, measured at 42.79 seconds in the follow-up baseline.
- Explicit objects and a private equality-transport lemma in OpenBaseChange
  reduced its named kernel probe from 52.14 to 21.16 seconds. The adopted module
  passes, and its public `.olean`, IR and C outputs match the original artifacts.
  The separate baseline timing wrapper failed after a host diagnostic; it does
  not establish a second clean whole-module build or a whole-module speedup.

The combined Tensor, Contraction, carrier and literal archive-consumer checks
pass against the fresh producer artifacts. Existing constructors and canonical
maps are unchanged. Contraction's public `.olean` and runtime outputs also match
the original artifacts; its helpers change proof implementation.

Abstraction must preserve the component reduction interface. Span now constructs
the source-total arrow inside a local constructor over abstract functors and
only then supplies the concrete Godement functors. The local `let` retains the
original component formula through beta/zeta reduction. Its naturality proof is
checked before the Godement objects enter the comparison. A separately applied
proof helper had instead reintroduced expensive conversion between the
preserves-zero instance proofs carried by the section isomorphism and freshly
constructed complex functors. The original component and quasi-isomorphism
consumers remain the acceptance checks for this boundary.

The full-subcategory boundary in Quillen's `FlasqueThirdSpan` exposed another
expensive conversion: identifying a lifted functor followed by the inclusion
with the raw Godement functor unfolded the large concrete construction. The
general [short-exact-sequence transport lemma](../Aglib/Algebra/Homology/ShortComplex/Subcategory.lean)
instead uses the actual supplied natural isomorphism and the `map_comp` law.
It preserves the original exact functor and its short-exactness certificate.

In two clients importing the same literal source prefix, kernel checking of
the generated exactness proof fell from 85.43 seconds to 0.098 seconds. Peak
resident memory fell from 12.84 to 2.57 GiB for the complete profiled clients;
each client checks both a separate certificate and the record, and detailed
profile export adds substantial overhead. These are controlled client results,
not whole-module speedup or CI resource measurements. The actual changed
`FlasqueThirdSpan` subsequently compiled in a focused Lake run in 219 seconds,
with only that leaf rebuilt. Its complete CI memory fit remains unmeasured.

## Recorded follow-up measurements

The first follow-up comparison starts from Aglib
`55b439b7219f12ad6ff2645b32d9f8b073dd8b28` and changes only
[Tensor](../Aglib/AlgebraicGeometry/Cohomology/Godement/Tensor.lean) and
[Span](../Aglib/AlgebraicGeometry/Cohomology/Godement/Section/Span.lean) in the
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

## Whole-library pass

The first aggregate pass covers all 1112 production modules and the requested
positive-test closure, 1136 modules in total, at `55b439b` with the retained
Tensor/Span changes. The ordinary rehashed build passes in 833.99 seconds with
6.17 GiB peak process-group RSS. It records 120 timed compilations and reuses or
restores the remaining artifacts. This is an incremental/cache-restoring build,
not a cold whole-library timing. The source/configuration snapshot remains fixed
through the run.

```sh
AGLIB_BUILD_THREADS=1 python3 scripts/build_serial.py \
  --receipt-dir /absolute/fresh/aggregate --rehash Aglib AglibTest AglibTest.AuditSupport
```

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
[WORK_PLAN.md](WORK_PLAN.md#heartbeat-and-compilation-performance-checkpoint)
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

## Why a short proof can be expensive

The kernel checks the elaborated proof and its type. In particular, it checks
definitional equality by reduction: two expressions can denote the same object
while requiring extensive unfolding to recognize that equality. An `Eq.refl`
proof can therefore be small while checking its use against the declared
equality is expensive. With nested functors, complexes and data-carrying category
instances, the important difference may be an implicit object argument or the
representation of a component's codomain.

The pinned [kernel implementation](https://github.com/leanprover/lean4/blob/v4.34.1/src/kernel/type_checker.cpp)
also compares proof types when applying proof irrelevance. Proof irrelevance
does not make conversion of those types free. Distinguish this work from
metavariable unification in the elaborator and from compiling executable code.

## Methods and evidence

| Method | When it can help | Evidence and limits |
| --- | --- | --- |
| Align object, codomain and instance representations explicitly | Different inferred expressions are definitionally equal but expensive to compare | The Tensor experiment above is direct local evidence. Extra annotations that elaborate to identical core terms need not help. Inspect the expressions first. |
| Generate explicit simplifier equality certificates | A `simp` proof leaves expensive reductions implicit | [Lean issue 14331](https://github.com/leanprover/lean4/issues/14331) reports a severe case improved by `simp -implicitDefEqProofs`. The pinned default remains `true`. Test only implicated calls and measure the complete declaration; this is not a direct replacement for a literal `rfl`. |
| Name repeated proof arguments before elaborating the statement and body | Large embedded proofs or differently represented proof types are repeatedly compared | The [primary-author discussion](https://leanprover-community.github.io/archive/stream/270676-lean4/topic/dsimp.20simplifies.20proofs.2C.20which.20is.20slow.html) explains both improvements and regressions. Its 0.06-to-10-second kernel regression concerned an experimental branch, not a demonstrated current compiler bug. |
| Use `as_aux_lemma` for identified duplicated proof terms | Proof bodies are duplicated in generated terms or simplifier results | The [pinned tactic](https://github.com/leanprover/lean4/blob/v4.34.1/src/Init/Tactics.lean#L13-L18) and [Mathlib examples](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Logic/Equiv/Basic.lean#L280-L291) provide the existing mechanism. Smaller terms can still require more conversion; abstraction is not an automatic kernel optimization. |
| Separate construction data from correctness proofs | Repeated large structures or generated correctness terms are the measured problem | Mathlib explicitly splits [projective resolutions](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/CategoryTheory/Abelian/Projective/Resolution.lean#L289-L310) for performance. Preserve the actual component formulas and consumers that unfold them. |
| Preserve useful regular definition boundaries | Kernel reduction order expands a large argument before a small wrapper | [Kernel reduction hints](https://github.com/leanprover/lean4/blob/v4.34.1/src/Lean/Declaration.lean#L17-L47) explain why `def` and `abbrev` can behave differently. Elaborator attributes such as `irreducible` are a different mechanism. True `opaque` data changes the reduction interface and requires deliberate API design. |
| Align parent instances and supply universe information | Diagnostics show instance synthesis or universe unification dominating | These primarily address elaboration. They are lower priority for the current kernel-heavy profiles; the presence of category instances alone does not diagnose an instance diamond. |

An especially relevant open lead is [Lean issue 14803](https://github.com/leanprover/lean4/issues/14803)
and its proposed [PR 14927](https://github.com/leanprover/lean4/pull/14927).
They describe fast elaboration followed by expensive kernel comparison of an
application with its eta expansion. The proposed change tries eta before delta
reduction. The PR was open and unmerged when inspected, and the pinned source
still uses the reported order. This is a diagnostic lead: Aglib's actual
conversion pair must match before attributing its cost to that mechanism.

Similarly, [PR 14770](https://github.com/leanprover/lean4/pull/14770) provides a
concrete wrapper-unfolding example. A merged PR is not sufficient evidence that
its exact implementation is present in a release: inspect the pinned source.
Do not change toolchains based only on an issue title or a historical speedup.

## A focused diagnostic procedure

1. Preserve compiled dependencies, the exact source and package options. Select
   one slow declaration rather than rebuilding the library. Separate imports,
   elaboration, tactic execution, kernel checking and output serialization.
2. Use native `trace.profiler` to identify named kernel tasks. In a scratch copy,
   enable `diagnostics` for the selected declaration to obtain kernel unfolding
   counters. The pinned [declaration checker](https://github.com/leanprover/lean4/blob/v4.34.1/src/Lean/AddDecl.lean#L183-L191)
   supplies the named `Kernel` trace. Counters identify repeated unfolding, not
   exact per-constant time.
3. Inspect the declared type and inferred proof type, including implicit
   source/target objects, category instances, eta expansions and proof-valued
   arguments. Determine whether forming the type or checking the proof causes
   the expensive comparison. Distinguish a large type conversion from a large
   proof term.
   A theorem-type probe should put the original proposition in a theorem binder,
   for example `theorem probe (_h : P) : True := True.intro`. Encoding it as
   `def probe : Prop := P` instead invokes nested-proof abstraction on the value.
   In the Cartesian investigation that introduced boxed `HasSheafify` proofs and
   inflated the probe's kernel work. Its corrected theorem-binder check takes
   7.55 seconds in the kernel; the earlier 73-second definition-value result
   does not establish intrinsic formation cost of the original theorem type.
4. Choose one mechanism supported by those diagnostics: matching explicit
   arguments, an explicit equality certificate, a named statement proof, or a
   narrowly factored construction. Preserve mathematical hypotheses, canonical
   maps and the standard heartbeat policy.
5. Compare full declaration/module kernel cost under the same inputs and check
   the immediate consumers. Keep a change only when it improves the relevant
   cost and preserves their required reduction behavior.

Module exposure is part of that last condition. Official [module documentation](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/)
explains why an imported public definition need not have an exposed body. A
locally successful rewrite can therefore fail downstream. Export useful
component equations when the interface needs them; do not compensate with
blanket `import all` or global exposure changes.

Caching reduces repeated work; parallel scheduling can reduce whole-build wall
time. Neither makes one pathological kernel conversion cheaper. Raising
heartbeats, adding more threads, changing `simp` indiscriminately or replacing
every `def` with `abbrev` is not a supported remedy for these observations.
