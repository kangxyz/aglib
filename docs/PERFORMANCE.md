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

## Equation proofs, presentations and structure fields

These cases were measured on 2026-10-18 while developing the projective
regularity, affine descent and Picard comparison families on the Picard branch. They concern
kernel conversions created by how an equation or a field is written, not
mathematical content.

**Differing proof terms of one equation.** In the Koszul exactness leaves of
`Cohomology/Projective/Regularity/`, three identities elaborated but hit kernel
deterministic timeouts at the default budget; with a local budget of 1000000 the
process aborted at the memory cap, and diagnostic builds reached 25.7 GB.
Profiling isolated the trigger: two occurrences of one coordinate multiplication
or transport carried distinct proof terms of the same degree equation. One
proof was written inline as `by …` in a statement; the other came from another
statement, or was abstracted from a definition body into an auxiliary lemma.
One restated lemma at variable degrees took 114 seconds and 25 GB; the same
statement with a named degree lemma took 2 milliseconds. After every degree
equation became a named lemma with atomic arguments (`koszulDeg_contraction`,
`koszulDeg_shift`, `koszulDeg_wedge`, `koszulWedgeEq`), and spelling conversions
were concentrated in `twistMerge`/`twistMergeInv` stated once at variable
degrees, `Regularity/Koszul.lean` dropped from about six minutes to 6.4 seconds
at a 2.5 GB peak. A candidate explanation, consistent with the next section but
not checked against a kernel trace: the two proofs have differently presented
types, so proof irrelevance still requires converting those types, and that
conversion reaches the twisting sheaves.

**A structure field compared through its unfolded statement.** In the affine
quasi-coherent descent of `Descent/Modules/Fppf/`, the kernel check of the
coherence field `nat_comp` of `specCompTransAlong` against a correct term
exhausted 9 GB even with the inner identity replaced by `sorry`. Stating the
field's proposition as a named definition (`Pseudofunctor.NatCompAlong`) and
building the structure with `CompTransAlong.mk'` made the kernel compare that
definition's arguments; the same check then took about 24 milliseconds in a
scratch probe. The earlier timeouts of the same family came from differing
proof terms inside `mapComp'` (`restrictAlong_mapComp'_hom._proof_*` against new
auxiliary proofs), the pattern of the previous case.

**Two presentations of one object.** In the same family, every comparison that
reached a component of `pullbackCongr` whose arguments were written in two ways
(`Scheme.Spec.map f` against `Spec.map f.unop`; `((specTransApp X).obj M).obj`
against `(tilde.functor _).obj M`) timed out, while each leaf identification
alone checked in seconds. The fix was a transport lemma generic in all of these
presentations (`natCompAlong_of_transport`), whose hypotheses are equations and
`HEq`s between the variables; at `Spec` each is `rfl` or `HEq.rfl`, the kernel
needs about 2 seconds, and the module builds in 22 seconds at 2.6 GB.

**Composites in two presentations.** In the gluing of rigidified pairs in
`Picard/Comparison/`, pulled-back line bundles have two presentations: Mathlib's
`Scheme.Modules.pullback` and the pullback pseudofunctor restricted along
`familyScheme p`. Single objects or morphisms compared across them checked in
milliseconds, but comparing composites (`≫`) whose implicit arguments differed in
presentation cost 7.4 to 15.3 seconds of kernel time per declaration in
development versions of `GluingDescent.lean`; a wrapper definition applied to one
side only gave no gain, and the diagnostics of one such check counted 491,372
unfoldings of `DFunLike.coe` and 435,930 of `ContinuousMap.toFun`. Those
development versions were not retained, so these figures rest on their build logs.
Stating each compatibility on both sides through the regular definition
`CategoryTheory.CompEq f g h := f ≫ g = h` (instances `CompTrans.RigCompat` and
`RigidifiedPair.PairCompat`), and converting presentations once at single
morphisms, brought every kernel check of the module below the 100 ms profiler
threshold; it builds in about 7.5 seconds. In `Comparison/Gluing.lean` the same
restatement cut `originPullback_nat_hom_app` from 21.9 to 12.2 seconds, but only
once the arguments inside `mapComp'` were syntactically the same on both sides
(22.4 seconds otherwise). Two lemmas whose cost appears to lie in their own
`rw`/`simp` proofs barely moved (7.73 to 7.28 and 6.97 to 6.65 seconds). A
candidate explanation, consistent with `lazy_delta_reduction_step` in the pinned
kernel but not checked against a trace: the kernel compares arguments before
unfolding only for constants with regular reducibility hints. `CategoryStruct.comp`
and the projections beneath it (`NatTrans.app`, `Iso.hom`) are abbreviations and are
unfolded down to the underlying data, whereas `CompEq` and `mapComp'` are regular,
so a mismatch directly in their arguments is compared argument by argument.

**Dimension comparisons at variable modules.** `Regularity/Mumford/HyperplaneStep.lean`
(then `Step.lean`) took 91 seconds to build, 77 of them in kernel checking:
`hyperplane_dim_le` 35.3 s, `hyperplane_dim_zero_le` 16.8 s, a connecting-map lemma
8.3 s, and three small `projectiveCohomologyDim` lemmas 3.7 to 5.2 s each. With the same
statements it builds in 9.6 seconds (a standalone profile: 9.0 s wall, 4.6 s kernel)
after four changes. Each dimension comparison is proved once, at variable modules, in
the owner of `projectiveCohomologyDim` (`projectiveCohomologyDim_le_of_surjective`,
`_le_of_injective` and `_eq_iff_injective` in `HilbertPolynomial/EulerCharacteristic`),
for the original linear maps `moduleCohomologyMapOfHom`. Coherence of the first term
`T.X₁ ≅ O(-1) ⊗ F` comes from `prop_of_iso` along the given isomorphism instead of a
`LinearEquiv` between `ModuleCat` carriers. The connecting-map lemmas are stated with the
linear maps. The cores of the two large lemmas are proved for a variable short exact
sequence and instantiated last (`projectiveCohomologyDim_zero_le_of_shortExact`,
`_one_le_of_shortExact`). The added lemmas cost in their owner what its existing small
lemmas already cost (five of the eight take 3.2 to 6.4 s of kernel checking each), so the
net saving is about 57 seconds: 81.4 s less for the step file (builds), and 21.1 s and
3.2 s more for `EulerCharacteristic.lean` and `Exact/Modules.lean` (standalone
profiles). A candidate explanation, not isolated: `projectiveCohomologyDim` is a
`finrank` under the local instance `moduleCohomologyModuleOfHom … projectiveConstants`;
each comparison makes the kernel unfold that instance to match the additive structure of
`Sheaf.H`, and at concrete modules one proof repeats the unfolding for every module
expression.

**Concrete degrees in a statement.** The twisting-functor authors reported that
elaborating a composite written at concrete degrees such as `1 + 0` timed out in
`isDefEq`, while the same composite at variable degrees and the instantiated
lemma elaborated at once. That probe was not retained, so this is an observation
rather than a reproducible measurement.

Practical rules from these cases: give each equation used inside `eqToHom`,
`pullbackCongr` or `mapComp'` one named lemma with atomic arguments and reuse its
proof term; state such lemmas at variable objects or degrees and instantiate last;
state a structure field that compares badly through a named definition; prove the
comparisons of a definition that carries a local instance once, at variable objects,
in the definition's owner, so that consumers only instantiate them; compare an
equation of composites across two presentations through one named regular definition
stated on both sides, keeping the arguments beneath projections (such as `mapComp'`
components) syntactically identical; and before
restructuring, separate elaboration from kernel cost with
`set_option debug.skipKernelTC true` in a scratch copy. A structural diff of the two
compared terms (a scratch tactic printing both goals) located each mismatch above
in seconds.

## Projective duality: typed boundaries before concrete geometry

The 2026-10-18 projective-duality continuation supplies further successful local
cases under the pinned toolchain. These are compilation results, not controlled
whole-library speedup measurements. The original canonical maps and mathematical
hypotheses were retained.

**Paste whole natural transformations before taking components.** In
[Trace/Local](../Aglib/AlgebraicGeometry/Cohomology/Duality/Projective/Relative/Trace/Local.lean),
`traceLocalHomFactory_refine` proves the restriction equation over abstract
categories, functors and supplied natural isomorphisms. The geometric proof uses
the actual whole affine-model comparison and only then takes its component.
This avoids repeatedly comparing expanded presentations at `Spec`. The maintained
Local, Gluing and original Core construction compiled successfully. It does not
by itself discharge every later residue or unit conversion. The newer
[affine descent transport](../Aglib/AlgebraicGeometry/Descent/Modules/Fppf/CompTransCoherence.lean)
uses the related method of identifying individual leaves by equations or `HEq`
inside one generic transport proof. Its final application passes `rfl` and
`HEq.rfl`; it does not ask the kernel to compare two large concrete composites.

**Separate the source, derived core and coefficient factors.** The canonical
[principal](../Aglib/AlgebraicGeometry/Cohomology/Duality/Projective/Canonical/ModelCharts/Principal.lean)
and [ambient](../Aglib/AlgebraicGeometry/Cohomology/Duality/Projective/Canonical/ModelCharts/Ambient.lean)
chart equations now use typed intermediate squares before the final paste.
For the ambient coefficient factor, normalize the native quotient-ring
presentation in the supplied equation and in the target separately, then paste
the resulting equation. A large final `rfl` or indiscriminate unfolding had left
that representation change implicit. Both maintained modules compiled. Their
private `principalWholeChartPaste` and `ambientWholeChartPaste` retain documented
400000-heartbeat allowances after measured 200000 failures; the public consumers
and other helpers use the default budget. Those finite allowances are part of
the measured boundary, not evidence that increasing a budget alone solved the
conversion problem.

**Transport dependent degrees before instantiating the geometry.** In
[Smooth/Trace](../Aglib/AlgebraicGeometry/Cohomology/Duality/Projective/Relative/Smooth/Trace.lean),
the direct all-degree proof failed even with a provisional 1,000,000-heartbeat
allowance. The retained proof first establishes
`purity_transport_eq_single_trace` for abstract abelian categories, objects,
functors and the original comparison family. It keeps the degree-zero input
literally at `0 + c`, instead of asking conversion to replace that index inside
reindexed morphisms. The private `singleReindexIso_output_inv_of_degree` adapter
eliminates an equality of the whole output-degree parameter before applying the
existing shift identity; it then specializes at `0 - d`. The actual geometric
formula and scalar-independence equation instantiate those typed facts.
Smooth.Trace and its final coherent consumer compiled with every declaration at
the default 200,000 heartbeats and recursion depth 1000. The original trace,
canonical isomorphism, all-degree statement and empty-source branch are unchanged;
no additional compatibility hypothesis or alternative derived model is introduced.
This is a successful proof-boundary change, not a controlled wall-time ratio.

**Use the original universal property before exposing a chosen preimage.** In
[Comparison/OpenTrace](../Aglib/AlgebraicGeometry/Cohomology/Duality/Projective/Relative/Comparison/OpenTrace.lean),
first prove the actual trace's top-homology equation, then lift that equation to
the installed bounded-below preimage. Attempting `change` directly through
`Functor.preimage` exposed its choice-based implementation. The retained proof
keeps that original preimage and trace; the complete open comparison and its
all-degree coherent consumer compiled.

**Check the representation and the failing phase before changing tactics.**
Explicit `CategoryTheory.Functor.comp_map` equations and pointwise isomorphism
cancellation closed the remaining coherent boundary wrappers. Fully qualify
`CategoryTheory.Functor.map_id` when a root `Functor.map_id` is also in scope:
the latter can be a different operation, rather than a slow categorical rewrite.
Inspect compact expression heads, implicit objects and selected instance names;
printing an entire derived-category expression can itself exhaust diagnostic
resources. A later successful declaration in a file with earlier errors is not
a successful module check.

Two fully expanded residue/unit corollaries remain unproved scratch candidates.
The published trace normalization uses the checked Core affine formula and the
original affine residue/unit laws; the final consumers already use those proved
interfaces. The failed conversion probes are not recorded as successful remedies,
and the expanded candidate declarations are not exported as proved theorems.

## Nonflat base change: share the concrete coefficient constructor

The original-map ring-equivalence transport in
[Map/RingEquiv](../Aglib/AlgebraicGeometry/Cohomology/BaseChange/Modules/Map/RingEquiv.lean)
first exceeded both 200,000 and 800,000 kernel heartbeats when rewriting the
concrete pullback-unit, composition and equality comparisons together. An
abstract commuting-triangle lemma checked at the standard budget, but its
five-line concrete specialization still exceeded 200,000 heartbeats: a short
application retained an expensive conversion between separately presented
coefficient composites.

The retained source defines `ordinaryPullbackCoefficientMap` once, including
the original unit and native comparison iso. Both the abstract triangle and
the concrete fibre-product coefficient use that same definition head. The
complete leaf then compiled at the standard 200,000-heartbeat policy in
18.2 seconds, with 2.51 GB peak process-group RSS and no guard failure. Both
public Epi and IsIso statements retain the original scalar base-change map
and require no additional flatness, quasicoherence or Noetherian hypothesis.
This establishes a successful proof boundary, not a controlled timing ratio
or a diagnosis of a compiler defect. The general proper-descent consumers
were still pending when this provider measurement was recorded.

The affine sheaf composition in
[Nonflat/AffineSheafComposition](../Aglib/AlgebraicGeometry/Cohomology/BaseChange/HigherDirectImage/Nonflat/AffineSheafComposition.lean)
exposed the same issue. Abstracting only its final categorical chain, and then
its complete functor calculation, still left the concrete specialization above
the fixed 25,600 MiB process-group limit. The retained
[AffineFunctor](../Aglib/AlgebraicGeometry/Cohomology/BaseChange/HigherDirectImage/Nonflat/AffineFunctor.lean)
defines one generic arrow constructor used literally in both the abstract
composition statement and the concrete `affineMapOfTilde`. The two native
composition transformations are supplied separately. The generic provider,
affine sheaf provider and composition provider then built in 1.6, 3.0 and
3.0 seconds, respectively, at the standard heartbeat policy; their complete
group peaked at 2.15 GB. The existing shared-iso definition of
`affineMapFromTensor` and its sections formula were retained. This validates
the composition providers; higher-image composition, refinement and global
descent are separate consumers and were still pending at this measurement.

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

## Failed cache probes and progress

In the pinned Lake, `Job.renew` preserves a failure while clearing its action
and log. A dependent job can consequently appear as a green `Ran` entry in a
failed `--no-build` graph. Treat that entry as blocked. Count validated native
output mappings and actual successful builds on the same inputs when reporting
progress. A probe's direct cache misses do not count all pending consumers.
For example, one 791-module probe had 678 valid mappings, 15 direct misses and
98 blocked consumers. Its confirmed progress was 678/791.

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

## Placement edits in widely imported modules

On 2026-10-18 the Picard-branch integrations placed reviewed general lemmas in their
natural owners by appending them to existing modules. Several of those owners are widely
imported. Counted over the import graph of `Aglib/`, their transitive importers were:
`Modules/Linear` 218, `ProjectiveSpace/Twisting` 210,
`Algebra/Category/ModuleCat/ChangeOfRings/BaseChange` 171,
`Cohomology/Functoriality/Modules/Composition` 111, `Cohomology/Modules/Scalars/Iso` 103
and `Cohomology/Exact/Modules` 94. The incremental `build_serial.py --rehash Aglib AglibTest`
checks of the last two merges (Mumford's bound, then the flattening inputs), each on top of
an already checked tip, recompiled 199 and 151 modules out of about 6,500 jobs and took 85
and 79 minutes. Most of that time went to projective-duality consumers that import those
owners: `Relative.Trace.Core` took 333 and 338 seconds and
`Canonical.ModelCharts.Principal` 418 and 547 seconds. The appended lemmas themselves
compile in seconds, and no older module can use them.

Place a new or moved general lemma in a new sibling leaf of its natural owner, in the
owner's namespace, rather than in an existing widely imported module; only the leaf's
actual consumers then depend on it. Before editing an existing module, count its transitive
importers, and edit a widely imported module only for a required change, batching such
edits. Docstring-only edits invalidate importers in the same way.

## Principal chart pasting at the CI memory budget

CI runs [39102309068](https://github.com/kangxyz/aglib/actions/runs/39102309068)
and [39108321624](https://github.com/kangxyz/aglib/actions/runs/39108321624)
failed in `principalWholeChartPaste`, at the native 12,800 MiB limit. The
previous local pass at a higher limit did not establish fit for CI.

The retained [Principal](../Aglib/AlgebraicGeometry/Cohomology/Duality/Projective/Canonical/ModelCharts/Principal.lean)
uses one private `WholeChartPasteData` value and six typed supplier equations.
The final categorical paste consumes those same projections instead of
reconstructing the concrete chart endpoints together. The original public
statement, chart arrows and supplier equations are unchanged.

Fresh local macOS compiles at the unchanged 12,800 MiB native limit passed
with one and four compiler threads. The four-thread check took 408.9 seconds
and peaked at 12,918.8 MiB process-group RSS, below the 13,824 MiB guard.
Its six comparable native artifacts matched the one-thread build exactly.
Scoped declaration, text-style and source-policy checks passed. These local
measurements do not give a controlled speedup ratio. The subsequent Linux
CI run [39115201867](https://github.com/kangxyz/aglib/actions/runs/39115201867)
passed the repaired Principal in 625 seconds, then exposed the same native
memory limit in `ambientWholeChartPaste` at `Ambient.lean:612`.

## Ambient chart pasting and affected consumers

The Ambient repair applies the same private typed-data boundary to the
original ambient chart arrows. Its six supplier equations feed the shared
projections directly; the public theorem and geometric comparison are unchanged.
A fresh local macOS compile passed at the original production settings:
four compiler threads, 12,800 MiB native memory, and a 13,824 MiB RSS guard.
The module took 257 seconds and peaked at 10,446.6 MiB process-group RSS.
Scoped declaration, text-style and source-policy checks passed. This is a
local budget result; the repaired Ambient has not yet passed remote CI.

An affected-consumer check toward `Relative.Smooth` then exposed an interpreter
memory failure in `ModelCharts.Descent.ChartSections`. An isolated diagnostic
reproduced it in `canonicalChartHomSection_repoint`: its factor rewrites,
reflexivity proof and final `congrArg` all completed before native checking
failed. Short tactic execution did not establish a cheap proof term.

The repair checks three literal factor equalities separately, then supplies
them and the original factorization equations to an abstract arrow-equality
lemma. The public Hom-section equality uses that private checked arrow equality.
The original public statement and arrows are unchanged, and the former local
400,000-heartbeat override is no longer needed. A fresh compile of the exact
main publication source, retaining its original `Descent.Sections` import,
passed in 24.45 seconds at four threads and the same CI limits, peaking at
3,162.84 MiB RSS. Scoped declaration, text-style and source-policy checks passed.

A successful producer check does not establish that its downstream modules
fit the same budget. Keep the downstream graph narrow, retain successful native
artifacts, and continue from the first failing consumer rather than rebuilding
the library.

Continuing this affected graph passed at the same CI limits: only
`Descent.CommonSections`, `Descent.Compatibility`, `Canonical`, `Smooth.Trace`
and `Relative.Smooth` needed compilation. The guarded group took 31.57 seconds
and peaked at 2,710.33 MiB RSS; unchanged suppliers were reused. This is local
coverage of the affected path, not a fresh whole-library or remote CI pass.

## Affine refinement through literal mate types

The nonflat higher-image [affine refinement](../Aglib/AlgebraicGeometry/Cohomology/BaseChange/HigherDirectImage/Nonflat/AffineRefinement.lean)
originally completed its tactics but exceeded the kernel checking budget.
Its retained proof uses the original composite pullback/restriction adjunction
and global-section faithfulness on the original higher direct image.

Give the pointwise helper private qcqs instance parameters instead of four
proposition-valued lets inside its result. Fix the bundled ring and bare
higher-image indices of its evaluators and mates explicitly, including the
immediate section suppliers. The public theorem derives those instances from
its given open pullback squares.

A Type-valued datum constructor still exceeded its local 800,000-heartbeat
budget after those changes. Removing that datum and applying the generic
faithfulness and cancellation theorem directly to the literal native objects
and arrows passed: 53 seconds for the Lean leaf, 56.71 seconds for the guarded
build, and 3.07 GiB peak process-group RSS. The j1/M24576/RSS25600 profile and
finite local bounds were unchanged.

This establishes the combined interface and proof-encoding repair, without
isolating one kernel conversion or preprocessing operation as its cause.
The public proposition is byte-identical and adds no hypotheses or maps.

The downstream local-refinement paste also exhausted kernel and elaboration
budgets when local natural-isomorphism aliases were converted into component
arrows at the final paste. Its retained proof gives the original component
hom and inverse arrows explicit module-morphism types and proves the functor
and cancellation algebra abstractly. The concrete application then checks at
the standard 200,000-heartbeat budget. Keep the large functor-level types out
of the concrete local context when only their component arrows are needed.

The same typed-component and abstract-pasting approach checks the arbitrary-open
composition leaf in 27 seconds (31.01 seconds for the guarded build), with
3.43 GiB peak RSS. Its concrete private paste still exceeded 200,000 heartbeats
during elaboration after the ordinary type-boundary repairs; a documented
800,000 bound on that private declaration sufficed. Other declarations and the
process limits stayed unchanged. This is a bounded elaboration cost, distinct
from a failure of the kernel to accept a completed proof.

Fresh checks at the CI profile (`-j4`, native 12,800 MiB, group 13,824 MiB)
also passed. The flat affine comparison took 112.91 seconds at 7.92 GiB peak
RSS; affine refinement took 43.40 seconds at 3.05 GiB; the proper endpoint
module took 69.82 seconds at 3.94 GiB. A coherent 51-module check reused valid
outputs and actually rebuilt affine normalization, global flat agreement,
open composition, naturality and restriction in 136.35 seconds at 7.80 GiB.
Each accepted run exited zero with no guard failure and its owned group gone.
These are local CI-budget checks, separate from remote CI publication.

## Remote resource calibration on the unchanged library

A Linux trial on 2026-10-19 used committed source
`b001ca8814edba7b56866202765094b724ad0c9e`, the pinned Lean 4.34.1 and Mathlib,
32 available CPUs and a cgroup memory limit of 120 GiB. Matching Mathlib outputs
were recovered first; Aglib started without compiled project outputs. These
observations concern that source and deployment, not a universal optimum.

The first library/test build admitted 16 frontends, each with `-j2 -M4096`,
under a 96-GiB aggregate RSS watchdog. It attempted 2027 compiler invocations
in 1441.75 seconds, averaging about 15 cgroup CPU cores and peaking at
41.3 GiB aggregate RSS. Nine modules reached their individual memory limit;
the requested whole-library targets therefore failed despite extensive valid
partial progress. A 4-GiB frontend limit is not a suitable blanket assumption
for this library. Successful outputs were retained.

Source-identical focused retries passed with larger limits:

- `Modules.QuasiCoherent.Affine.Morphisms` passed with `-j8 -M20480` in
  62.97 seconds, at 5.09 GiB peak group RSS.
- `MayerVietoris.Geometric`, `BaseChange.Modules.Naturality` and
  `Restriction.Open` passed together in 127.96 seconds under the same frontend
  profile. The low-budget run's companion kernel type-mismatch diagnostic in
  Mayer--Vietoris disappeared.
- `ProjectiveSpace.Differentials.Euler.MiddleFrame` and
  `Godement.TotalComplex.QuasiIso` passed together in 221.78 seconds under
  that profile. The earlier MiddleFrame type-mismatch diagnostic also disappeared.
- `Projective.HilbertPolynomial.EulerCharacteristic`,
  `Duality.Projective.Derived.Coefficients` and
  `Projective.TwistCohomology.Coefficients` passed together with `-j4 -M24576`
  in 522.04 seconds, at 16.03 GiB peak group RSS. Their reported module times
  were 179, 303 and 518 seconds respectively.

A continuation with ten frontends at `-j3 -M8192` completed another 155
production/test modules but found six further frontend memory failures.
Focused retries at `-j4 -M24576`, with at most three concurrent frontends,
passed all six unchanged: `Restriction.Coefficients` and `Godement.Section.Units`
in 133.00 seconds; the two canonical local-model modules, `Godement.OpenBaseChange`
and `DifferentialTrace.Restriction` in 657.19 seconds. The latter batch peaked
at 20.28 GiB aggregate RSS and averaged 2.25 cgroup CPU cores. Most of its tail
was one remaining compiler, not a shortage of available worker slots.

The subsequent library continuation retained the library's CI frontend budget
(`-j4 -M12800`) and admitted seven frontends under the 96-GiB aggregate cutoff.
Keep that per-frontend baseline when widening the pool; do not trade a known
working compiler budget for speculative concurrency. Heavy exceptions can be
retried separately without invalidating successful dependency outputs.
This continuation was stopped at the user's request after 1170.10 seconds,
with 107 new production and seven new test modules completed. Its peak was
29.58 GiB group RSS with seven frontends; average cgroup CPU use was 5.18 cores.
The requested stop returned exit 143 with its process group closed. Those
successful outputs were preserved; the whole-library targets remain incomplete.

No proof, statement, heartbeat setting or package option changed between these
attempts. Native thread counts did change, so these are successful resource
configurations rather than a controlled attribution to one parameter. A kernel
type diagnostic following a memory exception warrants a well-budgeted rerun
before changing accepted source. Continue missing consumers incrementally after
the actual failures are repaired; do not discard compatible outputs.

RSS sums also need careful interpretation. A sampled Lean process included
about 1.2--1.3 GiB of file-backed resident pages, much of it shared with other
frontends. The sampled container reported about 6.2 GiB anonymous memory and
10.3 GiB file cache. Per-process RSS sums count shared pages repeatedly;
individual `-M` settings are limits, not preallocated physical memory.

The last coefficient module remained on approximately one CPU after the other
two finished. Its source-level follow-up targets are
`twistingDerivedGlobalSectionsTensorCoefficientsIso_naturality`,
`twistingFiniteCechHomologyZeroSectionsIso_hom_augmentation` and
`twistingCechIntTensorCoefficientsMap_f_zero`. Their concrete conversion
boundaries, file-wide backward-defeq settings and implicit simplifier equality
proofs are diagnostic candidates, not measured causes. The last declaration
only transports an extension-by-zero component, so derived categories alone
cannot explain all three sites. Use the focused procedure above to locate the
named kernel task on the next otherwise-needed replay. A narrowly explicit
equality certificate or abstract component calculation needs its own kernel
check, component consumers and timed comparison before adoption.


## Isolate lint processes when checking several module origins

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

The [selected checker](../scripts/check_affected.py) now starts a fresh guarded
builtin-lint process for each selected module, and the
[declaration wrapper](../scripts/run_declaration_linter.py) starts a separate
Lean interpreter for each exact origin. The module selection, linter options,
exception handling and resource limits retain their existing meanings. Reuse
successful provider compilation when repairing this scheduling issue; the
failed lint does not require another proof build.
