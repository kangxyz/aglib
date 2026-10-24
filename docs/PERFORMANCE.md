# Investigating Lean compilation performance

This guide separates measured Aglib bottlenecks from candidate explanations and
records primary-source methods for investigating them. The compatibility basis
is Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. External issue states were checked on
2026-10-16. Historical reports do not establish a defect in the pinned compiler.
[Caching](CACHING.md) owns artifact reuse; this guide concerns the cost of
checking a declaration when compilation is necessary.

## Repair workflow

For serious compilation trouble, read the relevant findings here before trying
more fixes or increasing budgets. Match the symptom and source/toolchain
conditions; use the affected dependency's performance guide when it owns the
expensive construction.

If the guide does not cover the failure, search the corresponding upstream
GitHub issues, PRs and discussions, official documentation and linked author
reports. Start with Lean and Mathlib, then the affected library. Use distinctive
diagnostic text, public declaration names or the expensive phase (`whnf`,
`isDefEq`, instance synthesis, imports or serialization), with and without
version terms. For example, using [GitHub search qualifiers](https://docs.github.com/en/issues/tracking-your-work-with-issues/using-issues/filtering-and-searching-issues-and-pull-requests):

```text
repo:leanprover/lean4 is:issue "maximum recursion depth"
repo:leanprover-community/mathlib4 is:pr "synthInstance"
```

Replace the quoted terms with the actual symptom; also search this library's
repository and both open and closed results. Read the reproduction, discussion
and proposed code, then check the pinned source and release containing the fix.
Similar wording or a merged PR alone does not establish applicability.

After a repair passes the relevant incremental check, summarize it here:
symptom, affected declarations, versions/conditions, effective change, existing
validation evidence and source links, and remaining limits. Mark an uncertain
cause as uncertain; retain failed approaches only when they prevent repeated
work. Reuse existing measurements and compatible checks; no per-edit diary,
mandatory benchmark or extra acceptance run is required.

## CI cache reuse across dependency updates

[Quillen run 39969720587](https://github.com/kangxyz/quillen-k-theory/actions/runs/39969720587)
missed the whole-manifest Actions cache after upgrading Aglib and logged 3424
successful builds before its runner shut down. No Lean compilation error was
reported; cache saving was skipped after the shutdown. The shutdown cause is
unknown. Commit `5489643` had removed the separate toolchain-scoped restore,
leaving only exact toolchain/manifest recovery.

The existing restore now prefers matching pins, then the same Lean toolchain,
with legacy-key fallbacks so adoption can recover already saved generations.
The ordinary build uses `--rehash`; Lake decides applicability from current
inputs, rather than a GitHub cache hit establishing validity. Workflow fixtures
cover changed pins, legacy keys, preference order and platform separation.
This repairs cache selection, not runner shutdown or proof elaboration costs.

The first repair covered only same-repository Actions restoration. The native
migration had also removed Quillen's upstream-release import in `95270559`,
while the shared publisher retained a different `lean-native-*` format. Restoring
Quillen's older cache therefore did not acquire newly available Aglib outputs.
The shared native workflow now connects that publisher to manifest-discovered
upstream downloads, exact-pin/recent seeds and dependency-scoped `unstage`.
The native `-o` exporter records root-package outputs only, so inherited upstream
packages must be fetched separately too.

A bounded Lean 4.34.1 fixture exercised the actual workflow's stage, publication,
download and import commands for all three package scopes, with GitHub storage
replaced by a local transport fixture. A fresh consumer reused all three core
modules with `--no-build --rehash`, including an older Aglib producer at a newer
consumer pin. Its changed Aglib leaf correctly failed the no-build request and
compiled only that leaf. Forty workflow tests cover transport fallbacks and
identity, archive handling, immutable publication and existing check boundaries.
These are scoped transport/reuse results, not a whole-library CI pass or a timing
claim. The fix does not identify or prevent the earlier runner shutdown.

## Local validation and shared-artifact link metadata

The local input guard treated every ctime change as input drift. Creating or
removing a hardlink in a peer workspace changes the shared inode's ctime without
changing its content or mtime. A completed native command could therefore be
rejected before its success was recorded, repeatedly delaying the axiom audit.
A temporary-file reproduction produced the exact `Reflective input changed
during this attempt` error with unchanged hash, size and mtime.

The unified toolkit now treats ctime-only native changes as hash-cache misses:
rehash and retain a check only when content and lookup identity still agree.
Source/configuration temporal guards remain strict; genuine native-content,
inode, mtime, mode, symlink, disappearance and shadowing changes still fail.
Native evidence follows CI's trusted-producer content-correspondence contract
at observation boundaries, without claiming continuous mutation certification.
Existing compatible native check records keep their bindings. Ordinary checker
or Test failures collect independent axiom feedback and retain successful
categories for the retry; they do not authorize a successful aggregate result.

The active source, generator, cache and build implementations from all three
libraries now live in one `lean_ci` distribution. Thin current callers select
that package instead of importing retired scripts or checking old helper hashes.
The bounded regressions cover link activity during hashing/lint/reuse/export,
real mutations, failed checks, cancellation and managed-profile preservation.
A real Lean 4.34.1 import with 3902 observed native files passed while a peer
performed 210 hardlink operations; the before/after content binding agreed.
Scratch-installed package invocations exercise Git-free fixtures and the actual
three-library source entries, including reuse without rerunning those checks. These are tooling
results; no full mathematical rebuild or new acceptance cycle is assigned.

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

## Generated import entries and file-length limits

[CI run 39951693002](https://github.com/kangxyz/aglib/actions/runs/39951693002)
failed at `2c34f185` because the generated `Aglib.AlgebraicGeometry` entry grew to
3304 lines while retaining `set_option linter.style.longFile 3100`. This was a
source-style failure; completed compilation was saved, and Test/Publish skipped.

The minimal repair sets that import-only entry's `longFile` option to `0`,
following Mathlib's [explicit generated-root exemption](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Tactic/Linter/Style.lean#L379-L383).
Imports, ordinary implementation limits and mathematical checks are unchanged.
Under Lean 4.34.1 and the pinned Mathlib linter, a bounded native fixture reproduces
the 3100-line failure, accepts `0`, and still rejects an ordinary file at 1500.
This is scoped linter evidence, not a full-library CI pass.

Topic generation now uses the existing layout command's explicit `--generate
Aglib.Topic` mode. It always writes `longFile 0` for new and refreshed generated
entries; existing generated topics carry the same setting. It does not infer
exemptions from arbitrary proof-file contents.
Generator fixtures cover new and nested topics, source growth, ownership and
retained root/implementation bytes. Native root generation and CI are unchanged.

## Keep one representation of module sections

On 2026-10-23, the initial arbitrary-section nonvanishing implementation
reached the standard 200000-heartbeat limit at `whnf` while elaborating
restriction composition. This was an elaboration timeout. The accepted
[Nonvanishing](../Aglib/AlgebraicGeometry/Modules/Invertible/Nonvanishing.lean)
implementation states the comparison using one explicitly typed
`M : X.Modules`, changes the goal to its actual presheaf morphisms, and
applies the functor law:

```lean
change (M.presheaf.map (homOfLE k).op ≫ M.presheaf.map (homOfLE h).op) s =
  M.presheaf.map ((homOfLE k).op ≫ (homOfLE h).op) s
rw [Functor.map_comp]
```

This avoids asking elaboration to identify differently presented section
carriers while also reconstructing the composite restriction. In related
scalar and zero-section proofs, give `L.val` an explicit `X.Modules` alias
before using `.presheaf`, and retain that same `M.presheaf.map` expression
through the calculation. The bare expression `L.val` has syntactic type
`SheafOfModules`; switching representations in the last step introduced
field-projection errors or unnecessary conversions.

The original candidate `93b8d319` failed in native run
`remote-b5b40b72db8f4d7398c2fb40e082f3d3`. The complete repaired module,
SHA-256 `0b00b8a1d47a07013706469cf05ce96e797ffd3e759da8701aafbc045987b590`,
passed ordinary native compilation in
`remote-9fcb2011c37746649cfe2ac83c040e1a`: one compiler invocation and
11.14 seconds for the remote build action. All declarations retained the
standard heartbeat budget and their original maps and hypotheses. Several
proof repairs and cache conditions differ between the runs, so these
observations establish removal of the timeout, not a controlled speedup
ratio or a general attribution of compilation cost.

When the same boundary occurs elsewhere, align the actual module object,
section carrier and morphism presentation before applying a narrowly typed
naturality or composition lemma. Record the successful ordinary producer
compilation and its actual consumers under [normal proof iteration](DEVELOPMENT.md#normal-task).

## Preserve regular equations through conormal comparisons

On Lean 4.34.1, the unipotent-overlap comparison in
[RankTwoExtension/Conormal](../Aglib/AlgebraicGeometry/ProjectiveBundle/RankTwoExtension/Conormal.lean)
exceeded the default 200000-heartbeat limit during ordinary kernel checking
of `overlapConormalMaps_coordinate`. Abstract helpers, aligned section
carriers and a shared canonical map alone had not closed the specialization.

The passing implementation states both the abstract producer and concrete
comparison through the same regular definition `GlobalSectionImagesEq`.
Its arguments are the actual module objects, morphisms and original section.
The abstract frame-extensionality consumer accepts that same proposition;
its final application therefore retains the equation boundary at the
concrete spectral modules. Applying a wrapper to only one side would not
provide the same boundary. This follows the existing `CompEq` pattern below
and the pinned [kernel reduction hints](https://github.com/leanprover/lean4/blob/v4.34.1/src/Lean/Declaration.lean#L17-L47).
No new trace was collected, and no upstream compiler defect is established.

The localization calculations also use `Sections.translationOverlapPolynomial`
as the denominator of every inverse and lift. A separate
`overlapDenominator_algebraMap` states its coefficient equation using an
explicit `change` and ring-homomorphism laws. This avoids requesting an
instance for a differently expanded denominator inside an inverse argument.
The original maps and mathematical hypotheses are unchanged.

The failed source
`7b76a0eca7ab9cc764e6f32ac9c4dc686f6594c207897b02c1be38acf1d72f9e`
in native run `remote-f907e22742434203a1e1b46e479c1083` recorded the kernel
timeout at line 543, alongside denominator and rewrite errors. Source
`66f4b3a59348f687359b722c43295c569f9cd44843485c61d004d6037c80781e`
passed the complete Conormal module in 65 seconds in native run
`remote-ba6b25fe06e741aba407d12e644df10d`, with standard budgets and a
successful compiler exit. Other proof repairs and cache conditions differ,
so this establishes removal of the timeout on that module, not a controlled
speedup ratio or attribution to a single edit. The outer run failed on other
modules, including the separate global `Conormal.Compatibility` candidate;
that upper obligation was not covered by this pass.

The subsequent global frame transport retained the same regular
`FrameMapCompatible`, `FrameTransportSquare` and `PullbackFrameTransport`
equations in its generic proofs and actual consumers. Its final bare
`pullbackUnitIso_comp` rewrite still exhausted 200000 heartbeats at `whnf`.
Source `40fd6ed9804fc95d8fb6456c4aa92821f01c9caaad2076a5196de222c04a98db`
failed at line 593 in native run
`remote-4235fb93c0fe44f1ab828326a8daff66`.

Keep the typed naturality calculation and supply the exact composition fact
`pullbackUnitIso_comp a j₀` through `congrArg`, rather than asking rewriting
to infer the two scheme maps through the unit objects. After that repair and
removal of one unused simp argument, source
`edf1223ad5f5c00cc93161fbcb59fd92ecf9c4eee6c6e96e7cdd72567f98fc42`
passed the complete
[Compatibility module](../Aglib/AlgebraicGeometry/ProjectiveBundle/RankTwoExtension/Conormal/Compatibility.lean)
in native run `remote-123316c95d424e5d98b249b27da5de4a`, reported duration
278.45 seconds, at unchanged default budgets and without diagnostics.
The original morphisms and short exact extension hypotheses are unchanged.
This verifies the global conormal isomorphism and its original frame formulas;
it does not prove the later H¹-injection, GR vanishing or surface capstones.
No controlled timing improvement or profiled compiler-cause claim follows.

## Preserve module types in finite normalization

With Lean 4.34.1 and Mathlib `d13f23b`,
`integralClosure.finite_scalar_quotient_of_complete_local_normal_dimLE_two`
in [CompleteLocalSurface](../Aglib/RingTheory/IntegralClosure/PurelyInseparable/CompleteLocalSurface.lean)
reached the standard 200000-heartbeat limit at `whnf`. Its finite assembly
combined the literal product of local normalization images, the proved
kernel equality and quotient finiteness. Correcting intermediate product
instances alone had not closed this elaboration.

The passing implementation uses the regular named type `surfaceLocalImages`
and its named additive/module structures in both `surfaceToLocalImages` and
`isNoetherian_surfaceLocalImages`. A private regular proposition
`QuotientFinite Q` also appears in both the abstract kernel theorem and
concrete surface producer. The abstract theorem proves it using Mathlib's
`Submodule.CoFG.ker`; a separate abstract adapter matches the scalar
submodule quotient with `QuotSMulTop` once. The final surface endpoint
applies these shared statements. The private boundaries introduce no new
mathematical premise: finite local images, the original coefficient
actions, actual kernel and original hypotheses remain proved and unchanged.

Source `bf29b1f1d43c3e175cac7212d498a4813c01e79550164ea6605daaa80f32c4d8`
failed at `whnf` in native run `remote-ba6b25fe06e741aba407d12e644df10d`.
The complete repaired module, source
`8efdb286d5f297faa28e1191bd6ed57ed0c1cf133448389b8e571a667b851620`,
passed ordinary native compilation in 25 seconds in
`remote-df7e416c5dde4021b771d8c9cdddc29c`, at unchanged default budgets.
The outer graph failed on other modules. This establishes removal of the
tested timeout, not a controlled speedup, unique cause or general compiler
defect. Finite-type Nagata stability and resolution boundedness are separate
mathematical obligations.

The [all-finite-extension wrapper](../Aglib/RingTheory/IntegralClosure/CompleteSurface.lean)
encountered a related instance boundary at the concrete normal model
`B = integralClosure R F`. Asking for `Module B (integralClosure B M)`
reached the default 20000-heartbeat typeclass limit; manually choosing that
module exposed a parent-structure mismatch in the trace finiteness theorem.
Instead, `finite_of_finite_integral_model` proves the trace/transitivity and
integral-model comparison with `B` an abstract ring parameter. The concrete
consumer receives its conclusion over the original abstract base `R`.
No finiteness premise is added: all normality, fraction-field, finite-model
and separability hypotheses are supplied by the original field construction.

The explicit-module candidate
`138a15eb2b9b0c5bb47898d199b38d448f065f9ebc5f3ee72603ee50bcceb66e`
failed in `remote-68314ede6d02463d9b66ea5eb8be5993`. The abstract-model
version `a5558b461739c12d5958bbbf5d0b2e8afa51cc99e65c43884185d62b5f899e6a`
passed the whole wrapper in 17 seconds in
`remote-a32421a12426431ab6a42af7a2bda5a6`, with all default budgets. These
observations verify the repair on this source; they are not a controlled
comparison of individual instance-search paths or a general speedup claim.

## Retain the original map in ideal-power comparisons

The completed-base quotient comparison in
[FiniteTypeLocalComparison](../Aglib/RingTheory/AdicCompletion/FiniteTypeLocalComparison.lean)
originally normalized the native tensor `includeRight` from an `AlgHom`
through its `RingHom`, then rewrote `Ideal.map_coe`. The power-equivalence
declaration reached the default 200000-heartbeat `whnf` limit. The repair
uses `Ideal.map_pow` directly with the original `includeRight`, keeping the
same map in both the quotient producer and its consumers. Surjectivity is
composed with the existing exact quotient-map equation.

Candidate `dd06f3c14eb726e5444c61f03d616292541abc7132e81144d51e05e25819b3cb`
failed in native run `remote-68314ede6d02463d9b66ea5eb8be5993`. Repaired
source `4f11e3612242ef6443f0e5bcdefea7c194a7354f740bafaa1d31967f1d672cb0`
passed the complete quotient-comparison module in 10 seconds in
`remote-a32421a12426431ab6a42af7a2bda5a6`. Maps, hypotheses and budgets are
unchanged. This covers the compatible quotient comparisons; localization,
completed local rings and scheme stalk comparisons remain separate consumers.
The observations establish removal of the tested timeout, without a
controlled speedup or general attribution of compiler cost.

## Retain native localization structures

With Lean 4.34.1 and Mathlib `d13f23b`, the generic-ring comparison in
[ArcTermination](../Aglib/RingTheory/Blowup/ArcTermination.lean) encountered
a native `OreLocalization.instSemiring` versus fresh `CommRing` projection
mismatch, with an unexposed `OreLocalization.instAdd` in the diagnostic.
Its generic quotient-map specialization also exhausted 200000 heartbeats
at `isDefEq`. Source
`d98b1c8f0e6640f4f6843ace2b34d7bedba208728b4d2e18ecd410a703b03528`
recorded these failures in `remote-1f49812de3c9446db53b7f46d94f6bd4`.

The retained repair names the literal native localization with a regular
`arcGenericLocalRing` definition and exposes its native ring, algebra,
localization and local-ring instances consistently. Chart-map uniqueness
uses its sufficient semiring target. One `genericQuotientLift f S`
constructor serves both generic rings, and the comparison receives the
same actual ring homomorphisms into an abstract target. It no longer
converts between independently instantiated literal quotient maps.

Source `f69d9776e231497a5951eac41d27ae67c6ab564cacd230c4bf78ce14925d4720`
passed the complete module in 47 seconds in ordinary native run
`remote-4da3d88998fa431d8ee02bfe0cd45601`, with unchanged premises, maps
and default budgets. This removes the reported failures on that snapshot;
it is not a controlled speedup or compiler-defect diagnosis. The outer
graph failed elsewhere. Later minimal-generator and termination extensions
have separate source identities and coverage; full arc termination was
not proved by this pass.

## Preserve both affine unit comparisons in tensor-section transport

On the pinned Lean 4.34.1 / Mathlib `d13f23b7` basis, the actual affine
presentation row in
[AffineRow](../Aglib/AlgebraicGeometry/Blowup/ProjectivePresentation/AffineRow.lean)
exhausted 200000 elaborator heartbeats at `whnf` in
`pulled_tilde_spanSingleton`. Keeping the same unbundled module carrier at
every occurrence was insufficient (`remote-fc6fcc504e1e44568d2087416ccce62b`).
Carry both original `tildeSelf` comparisons explicitly. In particular the
source unit is transported by the actual pullback of `tildeSelf R` followed
by `pullbackUnitIso`; the proof no longer asks a concrete specialization to
identify pullback of the associated scalar module with pullback of the unit.

Concrete map-identity and unit congruence pastes then moved the timeout to
`affine_tilde_unit_triangle` (`remote-80e660ecc8564cbc93647fae9ed5ffa7`).
The successful boundary proves `unit_triangle_of_id` over an abstract functor,
with the actual unit arrows and their identity equations as parameters. A
single specialization uses the existing proved
`affinePullbackTildeIso_unitToUnit`. The original unit maps, full tensor ideal,
section reconstruction and epimorphic presentation remain the actual objects;
the equations are proved witnesses, rather than additional assumptions.

Exact Row source `a1b35d34009edc8eac0bf5f52c357e7fcd821f749c322117699a2c9b89bbcd2f`
compiled in 72 seconds in `remote-1e5790e91c584985854cb1ff33475be9`, source
snapshot `af9e59a97a25c21887eeee4ac29ff44ef8843e54dd01c4824de227bcec667a6b`,
under the unchanged 200000-heartbeat budget. No opacity, trust, premise or
resource-cap change, profiling or extra replay was used. The chart consumer
failed separately in that graph; this evidence covers Row, not the completed
projective embedding. Changed sources and failed baselines do not establish a
controlled runtime improvement.

## Retain the original pullback-row equation boundary

On the same Lean 4.34.1 / Mathlib `d13f23b7` basis, the concrete affine
restriction specializations in
[Restriction](../Aglib/AlgebraicGeometry/Blowup/ProjectivePresentation/Restriction.lean)
reached the default 200000-heartbeat `whnf` limit in both the quotient-cube
and framed original-row comparisons. Native run
`remote-72c0dd0ea2924206b5b28e7bf3d821ef` records those two failures. The
abstract cube argument alone did not prevent expensive conversion when its
result was pasted into the actual sheaf/module pipeline.

Use the same regular `QuotientRestrictionEq` and `RowRestrictionEq`
constructors in both the generic producer and concrete consumer. Their
arguments are the actual module objects, frame comparisons, quotient maps
and original sections. The concrete proof supplies established equations
for those arguments; it introduces no extra mathematical hypothesis.
Keep naturality at the exact component heads `(E.app M).hom` and
`(E.app D).hom`. A small typed `framed_naturality_paste` lemma composes
that equation with the original unit/frame/quotient arrows without asking
a final concrete rewrite to reconstruct their representations.

Restriction source
`fe89dc56d4a309ae3cae6d48b05cd7e0fdd2975a2c0cdfcdcf5477b4bab72b80`
passed ordinary native compilation in 301 seconds in
`remote-0cb9da7407c44157992bcd73c41985b2`, source snapshot
`577d7825be362af684667e2e6858ca1db5a6926544e93a794d8d86121c974de4`.
Default budgets, original maps and full ideal were unchanged. The outer
graph failed separately in ChartCoordinates, so this evidence covers
Restriction and its original row equation, rather than the complete
projectivity or contraction theorem. No profiling or extra replay was
performed. Different source repairs and cache states preclude a controlled
timing comparison or a general compiler-cause claim.

## Keep the completed-stalk equation through specialization

The tensor and arbitrary-scheme completed-stalk comparisons in
[Spec/CompletionLocalRing](../Aglib/AlgebraicGeometry/Spec/CompletionLocalRing.lean)
repeatedly reached the default recursion limit when a generic composite
of ring equivalences was applied to the actual stalks. Naming the
composite function alone did not close that boundary. Native run
`remote-540c701dce1447df9d7a70b82004351c` records recursion failures in both
the tensor and global specialization, alongside a separate affine-algebra
carrier error.

State the generic calculation and the concrete consumer through the SAME
regular `CompletionImageEq` definition, with the actual equivalence,
source/target completion maps, original stalk map and original element as
arguments. Its content is exactly `e (sourceMap s) = targetMap (originalMap s)`.
The `.eq` projection exposes that equality after an abstract equivalence
has been obtained. This retains the original map equation without asking
the specialization to normalize a newly expanded composite of stalk
isomorphisms, localization maps and completion equivalences.

For the affine chart, retain one raw ring carrier with its original
commutative-ring structure, and build the actual base algebra on that same
carrier. For the final point equation, retain the literal pullback and its
original projection, evaluate the proved chart-base equation by typed
`congrArg`, and compose explicit `Scheme.Hom.comp_apply` equations. Neither
step adds a flatness, normality, finite-type or completion-isomorphism
premise to the arbitrary-scheme completed-stalk comparison.

Source
`c8512946a69b5cad1b256cef8f274eae2f0a1edf293280ca38811abfbc39a894`
passed the full Spec module in 20 seconds in
`remote-0fb712b753214ed1bf3194b902d7a977`, source snapshot
`42b0e59dd8b032e4dc3b2ec827ff4f1eb84d81099ba7fa8756ef6aa0379d76df`.
The pinned toolchain and default budgets were unchanged. Coverage includes
the actual completed-stalk equation, residue-fibre correspondence and the
pointwise regularity comparison under the stated local finite-type
hypotheses. A subsequent proper global-regularity adapter is a different
source version and is not covered by this pass. Other modules failed in
the outer graph. No profiling or replay was used; these observations do
not establish a controlled speedup or a general compiler defect.

## Specialize the whole arc argument after fixing its algebraic data

The equal-count step in
[ArcTermination/Descent](../Aglib/RingTheory/Blowup/ArcTermination/Descent.lean)
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

## Cache independent chart producers before concrete geometry

When one concrete specialization blocks an incoming module, use its real
mathematical interfaces to separate independent producers. In the blowup
presentation, [ChartMap](../Aglib/AlgebraicGeometry/Blowup/ProjectivePresentation/ChartMap.lean),
[RowCoordinates](../Aglib/AlgebraicGeometry/Blowup/ProjectivePresentation/RowCoordinates.lean)
and [DegreeOneAugmentationChart](../Aglib/AlgebraicGeometry/Blowup/ProjectivePresentation/DegreeOneAugmentationChart.lean)
were separated from the scalar Rees specialization. The original namespaces,
actual maps and mathematical conditions were retained. Private coefficient
and preimage data stayed private; only the actual current consumer interfaces
were exported. The native Lake graph can retain each successful producer
when another module fails.

Run `remote-1b573df8ede942709d4c67dd6437e52e`, source snapshot
`aad4d3dd3fa636465cf368351715da01715d27f8fd2a0a9132ceb39cbbdd16bf`,
compiled ChartMap source `9e9765f2` in 3.4 seconds, RowCoordinates source
`9341ad2b` in 197 seconds and DegreeOneAugmentationChart source `4afe0736`
in 4.5 seconds, all at default budgets. ScalarChart failed separately;
its concrete consumer, embedding and final contraction theorem were not
covered. These are scoped reusable successes, not a completed-contraction
claim. Source and proof changes differ from the predecessor monolith,
so these measurements do not establish a controlled runtime improvement.
No standalone extra check, replay, client or profiling stage was added.

## Construct the tensor comparison inside the shared chart witness

The actual scalar Rees-chart triangle in
`Blowup/ProjectivePresentation/ScalarChart` exhausted the default 200000
heartbeats after the independent chart producers had compiled. Sharing only
`ChartTriangleEq` at the public producer and consumer still failed in
`remote-cd0528cad14b4f25bbce7027db079eae`. The first shared arrow witness
also failed in `remote-c854a529f942462a9cb03811e9b9e91d`: its Rees
specialization compared an independently constructed scalar `RingEquiv`
with the generic witness's expected tensor/localization types. That source
also contained an unavailable private-helper reference.

The successful `gradedChartArrowWithEquation` takes the original Away
algebra equivalence and constructs the actual tensor ring comparison
inside the generic constructor. It proves the coefficient square there,
pastes the native Cartesian chart square with the public Spec-square
lemma, and returns the actual chart arrow together with its literal value
equality and original scalar-map triangle. `scalarChartToProjData`
specializes this one constructor; the public arrow and both proofs project
the same witness. The actual chart-frame and augmentation consumers retain
the value equality as well as the projection triangle. The full tensor
Rees algebra, original row and geometric hypotheses are preserved.

In `remote-d74407bf6e1847f1842de9dd12c41ae9`, source snapshot SHA-256
`d3d754cb7deb6ce97d26c4d6c8e04cc3bada9c21145f064c9de64c3a62e9d8fa`,
`ScalarChart.lean` SHA-256
`a6306d446833da8fded31f22e9fb03b5ddd0b8c113543fcac649dacda2e63db4`
compiled in 128 seconds and its actual `ChartCoordinates.lean` consumer
SHA-256 `b5c032224be360aeece4818bd5902d82cac0dddf1e203d522a205ab637f4e378`
compiled in 113 seconds. Both used default heartbeat/synthesis budgets and
unchanged resource ceilings. This reuses ordinary proof-iteration evidence;
no profiling, replay, separate client run or controlled benchmark was added.
The whole Proper graph then failed in the newly reached `Embedding` module
on separate interface and instance errors, so this records the chart and
coordinate passes only, with no general-contraction completion claim.

The subsequent `Embedding` repair also keeps the complete restriction
comparison generic over the affine square and framed family before its
concrete section-ring specialization. It passes the existing epimorphism
proof explicitly to the original finite-family constructor. Unused finite
section instances are omitted only from the two private comparison lemmas;
the public finite embedding retains its needed finiteness hypotheses.
With `Embedding.lean` SHA-256
`27535326e5c4d925a4ff795cf112cca76cccbeb5d861395e949551ddb5148c22`,
run `remote-37836972b3b9498cb3ef9168b5fd58bd`, source SHA-256
`1ac63637a49c93bd5e981518ed64c89557b727966ac47f3119b739fd383332a8`,
compiled that module in 149 seconds and the original forward chain in
9.1 seconds at the standard budgets. That parent run then failed a
redundant rewrite in the upper projectivity assembly. Removing the rewrite
preserved the same base triangle. The final whole-Proper run
`remote-7ac9858abc3849a7bf9112dbadcdb71b`, source SHA-256
`ce5280f7f3740db61928d11a8fb9a2862efb26af108bc6bc9241510765251494`,
exited zero, compiling `Surfaces.Projectivity` in 7.6 seconds and
`Surfaces.Contraction.Proper` in 11 seconds. These are ordinary incremental
build observations; no controlled timing ratio or broader library checks
are inferred from them.

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

The historical command at that source revision was:

```sh
AGLIB_BUILD_THREADS=1 python3 scripts/build_serial.py \
  --receipt-dir /absolute/fresh/aggregate --rehash Aglib AglibTest AglibTest.AuditSupport
```

`AglibTest.AuditSupport` and that orchestration have since been retired. Current
production final checks use the native commands in [the local guide](DEVELOPMENT.md);
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

## Formal line-bundle algebraization: explicit transports

The positive-thickening isomorphism criterion in
[Formal/Algebraization/Detection](../Aglib/AlgebraicGeometry/Modules/Invertible/Formal/Algebraization/Detection.lean)
encountered a deterministic `whnf` timeout at the standard 200000-heartbeat
budget while reporting a dependent `simpa` mismatch. The same attempt also
failed to synthesize `IsIso` through a composite pullback functor and through
the native adic-system inclusion. This was an elaboration/diagnostic failure;
the log does not establish a kernel-proof timeout or a compiler defect.

The retained repair makes each transport explicit:

- Name the iterated-pullback `IsIso` proof and pass it directly to
  `NatIso.isIso_map_iff`, rather than ask instance search to identify the
  composite functor's map.
- Rewrite the ideal-sheaf index with the single typed equality
  `K ^ n = idealThickeningIdealSheaf f (I ^ n)` before supplying the existing
  proof. Avoid simplifying the entire dependent `IsIso` proposition through
  the local abbreviation `K`.
- Supply the `IsIso` of the adic diagram's actual natural transformation
  explicitly before reflecting it through `adicSystemToDiagram`.

The affected declaration is
`isIso_of_positiveThickening_pullback_isIso`. Its statement and original
geometric maps are retained, with no heartbeat override. The ordinary scoped
build of `Aglib.AlgebraicGeometry.Modules.Invertible.Formal.Algebraization`
then compiled both `Detection` and its rank-one consumer with no diagnostics.
The failed attempt is `remote-70faa5a11f2d47fd8616115436883985`; the successful
build is `remote-5f3f0f710ec04be4b365aad73b8fac39`, with source-content digest
`2a46c2ab76452bc5ee0f51d65b99ebb43c42a64a3a52350f84fe39fd0ab85e17`.
These are proof-iteration observations, not a controlled timing comparison.
The subsequent compatible-system effectivity consumer has its own build
coverage; this provider result does not certify that later assembly.

The native adic-system producer in
[Formal/System](../Aglib/AlgebraicGeometry/Modules/Invertible/Formal/System/Adic.lean)
exposed a separate **kernel** conversion failure. At the actual ideal
thickenings, checking the quotient comparison followed by pushforward of
the successor isomorphism exceeded the same 200000-heartbeat budget. Separate
`rfl` projection formulas and an `asIso` of the explicit composite did not
repair it: even the optional equation expanding the concrete transition to
its literal unit-composite body timed out. Failed attempts include
`remote-46eed2bae8f24172b2f7f75b78885174` and
`remote-10b5c78e07f949b79766c12512b8b725`.

The effective boundary uses the same regular constructors on both sides.
`Data.adjointCoefficientMap` defines the original adjunction-unit composite
at variable maps and coefficients. `Adic.coefficientReductionMap` and its
isomorphism/unit laws are proved at variable ideal, closed immersion,
coefficients and coefficient isomorphism. The concrete `positiveTransition`
and `positiveReductionIso` specialize these shared definition heads directly.
They no longer assemble concrete composites separately and then require the
kernel to identify their expanded projections. The unnecessary expanded
concrete body theorem is omitted; the generic original-unit formula and the
native reduction-unit law remain proved.

The actual bundle/successor-isomorphism interface, original units, maps and
mathematical hypotheses are retained. The final producer and its original
geometric-reduction consumer compiled in
`remote-f34b91ce82b341c389a8f38d77043f41`, two fresh successful frontends with
no diagnostics, at source-content digest
`40f30a1a9c4eb71bf7b2722e20e300681bbe6e536b99470b9dab848e37edf9ad`.
No heartbeat increase or additional replay was used. This locates an effective
proof-representation boundary; without a kernel trace it does not identify
an internal compiler cause, and the changed declarations do not supply a
controlled speedup ratio.

## Site cohomology: share the comparison definition, not only its proof

These entries retain the delivering author's reported native build observations
from the adopted source packet, at the stated source versions. The packet
contains source identities and status records; its historical timings are not
measurements made by the present integration run.

The native derived-section comparison gives a second instance of the
[shared-constructor boundary above](#nonflat-base-change-share-the-concrete-coefficient-constructor).
Generic coefficient-naturality lemmas compiled, but their concrete module-sheaf
specializations still exhausted 200,000 heartbeats at `whnf` or `isDefEq`.
Supplying explicit functors and universes, unfolding the concrete wrapper, and
using `simpa only ... using!` did not by themselves remove the expensive final
conversion. One diagnostic reported 77,412 reductions of `SheafOfModules.forget`
and 18,912 of each lifted-unit definition, but only 27 of `Functor.rightDerived`.
These are unfolding counts, not timings: they locate carrier conversion work,
not evidence that constructing the derived functor itself was the bottleneck.

The retained
[DerivedComparisonFactory](../Aglib/CategoryTheory/Sites/SheafCohomology/ModuleCoefficients/DerivedComparisonFactory.lean)
defines the **whole module-valued additive comparison** with its source object,
full functor and represented natural isomorphism as parameters. The generic
naturality lemma and the concrete terminal/scalar comparison definitions use
that same factory head. This avoids comparing independently elaborated
additive-equivalence chains after the native module carriers become concrete.
[DerivedGammaNaturality](../Aglib/CategoryTheory/Sites/SheafCohomology/ModuleCoefficients/DerivedGammaNaturality.lean)
then compiled in 8.43 seconds under the unchanged native guard. The source is
still native evaluation `rightDerived`, with actual `restrictScalars` where
required, and the same original Ext comparison; no new cohomology definition
or assumed comparison replaced it. This verifies the coefficient-naturality
fix, not every degree-zero, slice or boundary normalization using the factory.

The concrete degree-zero endpoint needed one further abstraction: the shared
factory and a generic H⁰ theorem still left a final carrier conversion, with
`DerivedTerminalZero` exhausting 200,000 heartbeats at `whnf`. In
[DerivedZeroPacket](../Aglib/CategoryTheory/Sites/SheafCohomology/ModuleCoefficients/DerivedZeroPacket.lean),
`moduleRepresentedPostcomp_ext_zero_of_eq` takes the **complete comparison `E`,
native unit value `y`, and original output class `z`** as parameters, together
with their equations identifying the canonical factory, unit and `Ext.mk₀`
class. It also retains the original section morphism and its equation under
the represented-section isomorphism. Rewrite these equations abstractly, so
the conclusion is literally `E y = z`, rather than reconstructing those
carriers during concrete specialization.
[DerivedTerminalZero](../Aglib/CategoryTheory/Sites/SheafCohomology/ModuleCoefficients/DerivedTerminalZero.lean)
then supplies the actual original comparison, section value and Ext class,
with `rfl` witnesses. The generic packet and concrete terminal/scalar H⁰ leaf
compiled in 5.58 and 8.42 seconds respectively, with stable source and clean
native guards. No concrete endpoint hypotheses, definitions, maps or budgets
were changed. This verifies these H⁰ endpoints, not the subsequent
`finalComparisonZero` consumer.
The same complete-`E`/`y`/`z` boundary, with canonical equality witnesses, also
made [DerivedScalarSlice](../Aglib/CategoryTheory/Sites/SheafCohomology/ModuleCoefficients/DerivedScalarSlice.lean)
compile in 78.57 seconds under a clean native guard, retaining the original
coefficient action and native chain restriction.

For the original module-to-abelian slice restriction square, abstracting only
the source map left another expensive conversion inside Ext: module restriction
followed by forgetting had to be compared with abelian restriction at the
coefficient object. The retained
[SliceNaturality](../Aglib/CategoryTheory/Sites/SheafCohomology/ModuleCoefficients/SliceNaturality.lean)
proves `extFullRestriction_square` over all four functors, including the actual
coefficient transport and its equation. It first proves
`toSheaf_overFunctorMap` at the sheaf-map level, then instantiates the complete
Ext equation. The leaf compiled in 87.68 seconds under the unchanged guard.
Carry both source and coefficient comparisons across the abstraction boundary;
do not leave their concrete object conversion for the final Ext rewrite.

A separate instance-synthesis failure required a different repair. Explicit
universes on the essentially-small-site Grothendieck theorem, and then on the
induced `HasSheafify` target, still left a constraint of the form
`u + 1 = max (u + 1) ?v` for `SmallModel`'s category. The retained
[Large/Injectives](../Aglib/CategoryTheory/Sites/SheafCohomology/Large/Injectives.lean)
first binds the original `smallCategorySmallModel` at the precise
`SmallCategory.{max u v}` type, then synthesizes sheafification and applies the
native Grothendieck supplier. This generic leaf compiled in 4.13 seconds.
Pin the category structure before dependent synthesis when this exact
max-universe ambiguity occurs; annotating only the final theorem may be too
late. This is not evidence for globally changing instance priorities.

These measurements are successful native leaf builds, not controlled speedup
ratios. Reuse their existing receipts; documenting the repair does not require
another compilation or a downstream blanket rebuild.


## Étale derived comparisons: share the equation, then specialize

These entries retain the delivering author's reported native build observations
from the adopted source packet, at the stated source versions. The packet
contains source identities and status records; its historical timings are not
measurements made by the present integration run.

The bounded-below étale comparison work on 2026-10-22 supplies two further
examples of the literal-boundary method above. These are native incremental
module results on the pinned dependencies, starting from Aglib `c6f64b5b`;
heartbeat and process caps were not increased. They establish successful
compilation of particular source versions, not controlled speedup ratios,
whole-library acceptance or a compiler defect.

### Exact-square conversion

A concrete proof of `derivedInverseImageSquareIso_exactComparison` in
[Derived/BaseChange](../Aglib/AlgebraicGeometry/EtaleCohomology/Derived/BaseChange.lean)
failed with `(kernel) deterministic timeout`. The generic exact-square proof
already compiled, but specializing a separately expanded concrete equality
still required an expensive native conversion.

The successful boundary uses `ExactComparisonSquareEquation` in
[ExactSquare](../Aglib/Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus/BaseChange/ExactSquare.lean):
a definition of the literal original equality, parameterized by the functors,
ordinary square, derived square and complex. The generic
`exactComparisonSquareEquation` proves that formula over abstract functors;
the concrete theorem states the same predicate and supplies the canonical
inverse-image comparisons. Only the named square constructors and equality
transport are normalized at the concrete boundary. The related
[UnitComparison](../Aglib/Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus/BaseChange/UnitComparison.lean)
uses `DerivedMateUnitEquation` in the same way. These predicates are explicit
equalities with proved witnesses, not replacement assumptions or opaque
certificates.

The repaired exact-square provider, unit-comparison provider and concrete
`Derived/BaseChange` leaf compiled in 2.6, 2.0 and 4.0 seconds, respectively.
The concrete leaf had previously failed after a 62-second task. Since the
baseline failed and the source changed, those times are not a speedup ratio.
The actual square, original units, universes and mathematical hypotheses remain
part of the interface.

### Cocycle elaboration

A concrete cocycle comparison in
[PullbackComposition](../Aglib/AlgebraicGeometry/EtaleCohomology/PullbackComposition.lean)
instead exhausted the elaborator's `whnf` limit of 200000 heartbeats. This is
not the preceding kernel-timeout diagnostic. The successful refactor moves the
cycle-class map law to `HomologicalComplex.addCommGrpCycleClass_map` and the
Ext/right-derived comparison to
`InjectiveResolution.extRightDerivedAddEquiv_cocycle_natTrans` in
[CocycleComparison](../Aglib/Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus/BaseChange/CocycleComparison.lean).
Their arguments are abstract complexes, an injective resolution and an additive
natural transformation. The concrete application supplies the original
constant-integer/global-sections transformation instead of repeating its
resolution and homology calculation inside the scheme-specific proof.

The generic leaf compiled in 2.7 seconds. Subsequent normalization repairs and
specialization yielded a successful 169-second `PullbackComposition` compile,
including the equality of the original all-degree cohomology pullback with the
actual canonical derived-global-sections pullback. Generic acceptance alone did
not establish that endpoint; its concrete module had to pass too.

Use small reusable lemmas with explicitly typed arrows and the same literal
formula on both sides of the abstraction boundary. Import their owning leaves,
retain successful dependencies and continue only the affected incremental graph;
a documentation update creates no new compilation or validation obligation.

### Degree-zero specialization: preserve the actual maps as parameters

The concrete degree-zero comparison still hit a native kernel timeout in the
run that accepted `PullbackComposition`. Sharing the conclusion predicate and
then the unit/transport input predicates did not suffice: the next concrete
specialization also timed out, despite acceptance of its generic provider.

The successful boundary in
[ActualZeroComparison](../Aglib/Algebra/Homology/DerivedCategory/RightDerivedFunctorPlus/BaseChange/ActualZeroComparison.lean)
keeps the actual ordinary, derived and higher exchange maps, comparison
isomorphisms, and source/target transport arrows as typed abstract parameters.
Separately proved canonical equalities identify these parameters with the native
mates, comparison isomorphisms and transport formula. Substitution of those
witnesses occurs only in the abstract proof, not in the large concrete sheaf
calculation. Here “opaque parameters” means abstraction by theorem arguments,
not changing the canonical definitions to Lean `opaque` declarations.

The generic `higherExchangeZero_normalization_actual` and its actual-unit
adapter compiled in a 2.0-second provider task. The concrete leaf next accepted
five canonical alias lemmas: the ordinary mate, native derived adjunction,
derived mate, higher-direct-image comparison, and higher-map transport
identifications. The final `Derived/BaseChange` leaf then compiled in 11 seconds
on 2026-10-23, including `higherBaseChangeMap_zero` for the actual canonical
maps. This last consumer acceptance, rather than the earlier generic or alias
acceptance, establishes the successful degree-zero specialization.

No mathematical assumptions, maps or resource caps were added or changed, and
no separate kernel replay was used. This is a successful compilation boundary,
not a controlled speedup ratio or acceptance of every derived coherence target.
The lesson is stronger than naming a proposition: preserve the actual map and
comparison arguments throughout the concrete application, and move their
canonical substitutions behind the generic boundary as well.


### Native whiskering conventions for higher horizontal pasting

The final 2026-10-23 continuation adds a precise convention to the same method.
For nested coefficient prewhiskering and homology postwhiskering, the generic
supplier must return the consumer's literal `whiskerLeft J (whiskerRight β H)`.
Normalize `Functor.whiskerRight_left`, `whiskerLeft_twice` and
`whiskerRight_twice` over abstract categories while retaining the required
associators. Substituting concrete exchange arrows before this normalization
left the delivering author's higher-horizontal witnesses at a kernel
`deterministic timeout` in runs119 and121.

Even a concrete `congrArg (whiskerLeft P)` factor proof could retain expensive
conversion. `HigherWholePasting.mapped_horizontal_second_native` accepts the
original unwhiskered source-comparison and exchange equations, constructs their
whiskered forms in the abstract helper, and returns the native convention.
`whole_second_reassociate` handles the last comparison-source association.
Assemble the whole transformation before extracting its final component.

The corrected generic provider compiled in delivery run123; run124 then
compiled the raw concrete leaf. Final run125 compiled HigherWholePasting in
2.9 seconds and the complete Derived/BaseChange consumer, including
`higherBaseChangeMap_hComp`, in228 seconds. The two final source hashes are
`513e0413705b92c3950dd8f0151fc63917d0e52a9a9fdee1196ef3386b8b3258`
and `9833e77023b1d94956a783e83d2d89446e842dd864d112d91e19e79ab876ff31`.
These are retained author observations from archive
`etale-coherence-source-20261023T040650Z.tar.gz`, with source and log records;
the failed diagnostics do not state a numerical heartbeat budget. No source
budget override, replay or new benchmark was used, and no speedup ratio or
compiler-defect claim follows from the changed-source observations.

### Higher exchange components: retain the whole transport equation

The original higher-exchange consumer in
[`Proper/Reduction/Composition`](../Aglib/AlgebraicGeometry/EtaleCohomology/Proper/Reduction/Composition.lean)
encountered a kernel `deterministic timeout` when a concrete `change` exposed
its source isomorphism, mapped original derived mate and target isomorphism
at once. On Lean 4.34.1 and Mathlib `d13f23b7`, run
`remote-976f2775cb4446c5a5bb25b1d9d7739a` failed this Composition leaf
(source `aae7ec921785deb277e91f4571ffadc411beee2762332361fad90c50f7efab6b`);
Lake reported 152 seconds for the module. The standard 200000-heartbeat
budget was retained, and no OOM was observed.

The repair proves `isIso_app_of_whiskered_transport` over variable categories,
functors and original transformations. It accepts the literal whole equation
`δ = s.hom ≫ whiskerLeft J (whiskerRight β H) ≫ t.hom` and invertibility
of the original `β.app (J.obj X)`. Only that typed helper expands the native
whiskering component. The concrete consumer supplies the existing whole
`higherBaseChangeMap_eq_transport` and preserves its original coefficient,
source/target comparisons, derived mate and four derived-category universes.
It needs no concrete component conversion or new premise.

The repaired source
`1b0b3c0166c0ade282a78d7ac80bc78029920e179f96f26f5374f524eeab856d`
compiled in 5.5 reported module seconds in
`remote-e3f48a4100624625bb4632ca1f4d0ce0` with the unchanged standard budget.
That batch accepted Composition and Retracts but failed a separate record-layout
error in InjectiveRetract; it was not a successful three-leaf run. These are
source-bound incremental observations, not a controlled speedup benchmark,
compiler-defect claim, new profile or kernel replay.

### Finite Ext tests: isolate witness selection

In
[`Ext/BiproductComparison`](../Aglib/Algebra/Homology/DerivedCategory/Ext/BiproductComparison.lean),
the actual `Ext.addEquivBiproduct` source and target equivalences were already
typed at their original coefficient carriers. Selecting componentwise
preimages inside the specialized surjectivity proof still exhausted the
standard 200000 heartbeats at `whnf`. This occurred in
`remote-8c4ef9011fcb408e8cb017d79e1d1137`, source snapshot
`4ec8c76c3be06c267eba21d07018946fabe806ddeb4ab4d467c468df33c99b35`;
the subsequent unknown-constant error was cascading.

The validated repair puts witness selection and inversion of the product
equivalences in private `surjective_of_pi_transport`, parameterized by plain
functions, two actual equivalences and their literal component equation.
The Ext consumer supplies its original comparison, native additive
equivalences and original coefficient-naturality equation. The public
statement retains arbitrary finite-index universes, independent Ext sizes,
a preadditive source and an additive coefficient functor; no premise or
budget is added.

The exact repaired leaf
`8851e330dd2ae53f1b26f3876078379849302c51a5f3e9d12eb3a6697229fb77`
compiled without diagnostics in
`remote-1aca77219a7c4e619c3b814d976be5be`, whose source manifest
`6b15739f5f2dc67137f8e663a118c2b0904f8cd1a47f96768f1d2a127a9fdd1d`
contains that leaf hash. Its one frontend succeeded; recorded wall time was 7.7 seconds. These are changed-source compilation
observations, not a controlled benchmark, new diagnostic run or kernel replay.

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

## Values at concrete fibre products over `Spec (CommRingCat.of A)`

In the flattening-stratification work of 2026-10-19, kernel checking was slow for declarations
whose values or proofs involve a fibre product over `Spec (CommRingCat.of A)`, such as
`pullback (toSpec A ι) (Spec.map (CommRingCat.ofHom σ))`. Retained probes on the pinned toolchain
against compiled dependencies, at profiler threshold 50 ms, measured the following.

- The definition `moduleCohomologyGlobalScalars (pullback p (Spec.map (CommRingCat.ofHom σ))) N q`,
  at its inferred type, took 3.2 seconds of kernel type checking. The same definition over
  `pullback p g`, with `g : Z ⟶ W` variable, stayed below 50 ms.
- The same terms inside theorem binders (`theorem probe (_h : P) : True`) checked in about 13 ms
  together for `pullback p (Spec.map _)`, `pullback p g` and `P^n_A ×_{Spec A} Spec B`, including
  `Module.Projective B` of `H^q` with its structural action.
- Restating the base-change part of `IsFiberBaseChangeBound` at one point and proving it by
  projection from the bound took 16 seconds; the vanishing part took 12 seconds. The same
  proposition as a theorem binder stayed below 50 ms.
- In `FlatteningStratification/Flatness`, the uniform comparison lemma took 28.6 seconds and
  `directImageTwistSectionsLinearEquiv` 8.1 seconds.

The diagnostics counters for such declarations are dominated by additive-structure projections
(`Functor.obj`, `AddCommGrpCat.str`, `AddGroup.toSubNegMonoid`, `DFunLike.coe`) and include
`Function.Injective.addCommGroup` several thousand times; Mathlib transports the group structure
of `Ext` along `homEquiv`. The conversion pair has not been identified. A candidate mechanism,
unverified: the kernel compares two presentations of the additive structure on `Sheaf.H`, and
with a concrete base the delta order unfolds `Spec` and fibre-product data.

Forming statements over concrete fibre products is cheap; checking values and restated proofs
over them is not. Let one theorem consume the defining hypothesis directly, keep restatements and
definitions at `Spec (CommRingCat.of A)` few, and state helpers at variable data, as in
`PullbackComposition`. Before attributing a cost to a fibre product, separate statement
formation from proof checking with a theorem-binder probe.

## Declaration lint memory in CI

On 2026-10-19 the CI job for `c6bddf7` was killed by the resource guard (exit 137, RSS cutoff
13,824 MB) about six seconds into the Batteries declaration linter, after Lake's builtin lint
phase had finished. The previous push, `9645827`, passed the same step. CI ran both phases as one
guarded `lake lint -- --no-build`. Measured separately on the remote Linux builder at `df4680e`,
the builtin phase (`lake lint --builtin-only`, which loads the `Aglib` and `AglibTest`
environments in the Lake process) peaked at 8.7 GB and the driver (`runLinter --no-build Aglib`)
at 6.4 GB. A candidate explanation, consistent with these numbers: the Lake process keeps the
builtin phase's imported environment mapped while it runs the driver, and the guard sums the
resident memory of its process group, so the library's growth by a few dozen modules moved the
sum past the cutoff. CI now runs the builtin phase and the driver as separate guarded processes.
Keep separately guarded commands for phases that each load the whole library.

A standalone full-library timing on 2026-10-20 used source `4282748`, Lean 4.34.1,
and existing local macOS artifacts for 2,128 production files plus the `Aglib`
root. `lake --no-cache --rehash --no-build build Aglib` first verified the native
graph in 13.17 seconds without compilation. Running Batteries separately as
`lake env lean --run .lake/packages/batteries/scripts/runLinter.lean --no-build Aglib`
then passed in 144.34 seconds, with 6.32 GiB peak owned-process-group RSS, one
Lean thread, a 12,800 MiB frontend cap and a 13,824 MiB group cutoff. Both guards
reported successful process-group closure. This measures the declaration pass;
builtin lint, standalone text style and axiom audits are separate costs. A
seven-origin isolated declaration run had taken 44.72 seconds at 4.51 GiB;
repeated environment loading means its per-origin average does not predict a
single full-library pass. Whole-environment and exact-origin lint coverage also
retain their distinct environment/policy premises.

Under the same cached source and limits, full builtin lint took 17.39 seconds
at 3.55 GiB for `Aglib` and 13.63 seconds at 4.49 GiB for `AglibTest`. The fixed
auditor over origin prefixes `Aglib` and `AglibTest` passed for 35,401 declarations
in 15.62 seconds at 5.72 GiB, including its 16 private/generated controls. The
positive-test cache-only graph check took 6.42 seconds. These measurements
support batching and separate processes rather than a new result-cache system.

An initial whole-`AglibTest` Batteries declaration pass took 15.71 seconds
at 5.47 GiB and exposed 30 existing issues: 21 definition names, five missing
docstrings and four deliberately specialized unused instance arguments. The
cleanup renamed the definitions, added the documentation and explicitly named
the intentionally unused regression instances with leading underscores, as the
pinned linter permits. Statement types, hypotheses and proof bodies were
preserved. Only the 18 changed test leaves and their umbrella were recompiled.
The complete test declaration pass then succeeded in 15.86 seconds at 5.46 GiB;
changed-source style, test builtin lint, the full origin audit and rejection
controls also passed. CI now runs this test umbrella pass once alongside the
production declaration pass, with their separate environment predicates.

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
named task during the next otherwise-needed native compilation. A narrowly
explicit equality or abstract component calculation needs successful ordinary
compilation of the affected producer and actual consumers before adoption.
Keep separate profiling or controlled comparisons to an explicitly requested
performance investigation; they are not another acceptance chain.


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

## Binary-form section and geometric-point typing

On Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`, the new
`ProjectiveSpace.BinaryFormProduct.Fibers.surjective_of_geometric_point_lifting`
proof exhausted 200000 elaborator heartbeats at `whnf` in
`remote-e0d45d58b1ae4817876f8ce2b2f66f61`. The final application of
`Scheme.fromSpecResidueField_apply` had only inferred arguments. The successful
proof explicitly names the point obtained through the original
`Spec.algebraMap`, supplies the original residue point and both explicit
arguments to the native lemma, and annotates categorical pullbacks occurring
inside `Finite` as `: Scheme`. The latter annotations prevent elaboration
through the category of types. The scope owner recorded the unchanged geometric criterion compiling
in 4.7 seconds in `remote-b24285e7546a4c7ba4ad15c6087a07db`.

The same run exposed a separate `Lean.Meta.acLt` heartbeat failure in
`BinaryFormProduct.LocalCoordinates.transitionUnit`, where
`simpa only [mul_comm] using hzw` compared concrete section-ring products.
The exact term `(mul_comm w z).trans hzw` proves the same inverse identity.
The scope owner recorded `LocalCoordinates` compiling in 5.1 seconds in
`remote-095c0a8fd69f4c3aa97f9e7764122554`. The upstream
[simplifier implementation](https://github.com/leanprover/lean4/blob/master/src/Lean/Meta/Tactic/Simp/Rewrite.lean)
shows permutation-rule ordering through `acLt`; that current source supplies
background, without establishing a defect or an applicable upstream fix in
the pinned compiler.

The final finite/surjective endpoint batch
`remote-36e7150d5e5e4dce8167addfc4fc81ed` compiled four changed leaves with no
diagnostics on source digest
`a2769aeb58683a14eaaa45e52a11d27d1bed2555759e5afd58e007bd8bd13a8f`.
All original maps, universes and mathematical conditions are retained, with
the standard heartbeat budget. These are successful proof repairs, not a
matched benchmark or a compiler-defect diagnosis; no extra acceptance run
was used.

## Typed evaluation of coefficient-map composites

The same typed-transport boundary also applies to evaluating concrete
represented-coefficient pullback equalities. The development provider
`EtaleCohomology/H0/ProperHenselian/Sections` exhausted 200000 elaborator
heartbeats at `whnf` when `ConcreteCategory.congr_hom` specialized the final
concrete unit/comparison composite. The scope owner observed this in
`remote-a435e19647de4064a96b9a7dbadcc452` and
`remote-e7a6a8ffcc8d40558b0e9df7db85b6ad`.

Keep the complete original arrows, input and output as parameters of a generic
helper:

```lean
private theorem eval_composite_of_eq {P Q R : AddCommGrpCat.{v}}
    (p : P ⟶ Q) (q : Q ⟶ R) (r : P ⟶ R) (h : p ≫ q = r)
    (x : P) (y : R) (hr : r x = y) : q (p x) = y :=
  (ConcreteCategory.congr_hom h x).trans hr
```

The concrete use supplies the proved categorical equality and a reflexive
pure represented-output equation. The original pullback, represented-sheaf
base-change isomorphism, coefficient unit and terminal transport are retained;
no concrete inverse-image carrier has to be reconstructed inside evaluation.
The owner recorded one successful provider frontend in 8.17 seconds in
`remote-d28c35d131cf46d6b38802fcabe27be4`, on source SHA-256
`d5e6e1e087d66bd805dab2c0e6d19f91ad4817437c25d4a4adcc52cee6326469`,
without a heartbeat increase. This is evidence for the actual completed
section-comparison provider. Its subsequent proper-henselian H0 and torsor
consumers were not completed by that invocation. These observations extend
the existing typed-transport finding; no matched benchmark or extra run was
introduced for the note.


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

## Augmented Amitsur differentials and typed tensor coordinates

At Lean 4.34.1 and the pinned Mathlib revision, specializing
`CochainComplex.of_d` at the augmentation degree failed to elaborate the literal
degree-one codomain in [Augmented](../Aglib/Algebra/Homology/Amitsur/Augmented.lean).
The diagnostic exposed different presentations of native `Nat` addition and
one projections. The retained proof first establishes the zero composite with
the actual alternating coface differential. It unfolds only
`CochainComplex.of.d`, splits its condition, and rewrites the zero composite
before the native `eqToHom` transport. The original complex and augmentation
are preserved. Broad simplification and a private import-all attempt were not
adopted.

Failed run `remote-772d892e9490429d84615f3e48a07a79` has source digest
`aa1eb091b74dea36b446b2e3792c7145dc9deb709067687b00729ff5bd54232e`.
The repaired provider passed in 2.7 seconds in
`remote-2e30c4f1fceb4bce836fd0353fc61b09`, source
`c8d8bb40c1ea4f15363248b8b372c68971e76e6fd3a8028f7345e1e8caee333b`.
Separate downstream failures in that invocation are outside this success claim.

The scalar extra-degeneracy equations also failed when rewriting partially
unfolded native wide-pushout and tensor objects. In
[ScalarExtension](../Aglib/Algebra/Homology/Amitsur/ScalarExtension.lean), retain
the actual typed objects `S ⊗[R] A` and native algebra tensor maps.
`scalarTensor_eq_native` still identifies this functor with the original
`MonoidalCategory.tensorLeft` by `rfl`. At the first face, compose the original
inclusion and map equations through a short `calc` chain instead of asking
rewriting to reconstruct the hidden colimit objects.

Run `remote-37d1cb4eff6e4d14b893481c5134a0b3`, source
`f204874a98f04592be5ff66d44c0266b4b6d4e2d7a201586f2eb62d9b0e4b87f`,
exposed the failed implicit-transparency boundary. The repaired provider and
actual Coordinates consumer passed in 8.5 and 5.7 seconds in
`remote-a7f7aa6f9de44059b3e32dce7706c6f3`, source
`e76b8b6d4b1b7e7adace25ab99c0fe513ff707809eb974f7310fafa7517a2a4c`.
The separate Comparison consumer was still failing there. The final Amitsur
root subsequently passed in `remote-a31efd3dee9642bc9849f4e6cb6efc59`.
These observations do not isolate a compiler defect or a controlled speedup.
No resource budget or mathematical premise was changed.

## Evaluate original geometric-stalk units through typed projections

The concrete `germ_nativeStalkIso` proof in
[InverseImage](../Aglib/AlgebraicGeometry/EtaleCohomology/GeometricPoints/InverseImage.lean)
exhausted the standard 200000-heartbeat budget at `whnf` while rewriting the
skyscraper-unit and product-projection equations. The same failed invocation
also could not expose the native `getLimitCone` coordinate under implicit
transparency. Run `remote-6650b3f43f4d4c8cab861c845d46666e`, source
`02e7d71b78e61458e983cf345c865d595708d95991da2b34f3ebce8c3ae48cf9`,
still supplies successful Skyscraper-provider coverage only.

First evaluate the native point's skyscraper unit through its fully typed
presheaf arrow and constant-product projection, retaining the original
`toPresheafFiber` germ. Then apply the bounded `projection_composite` helper
with all six arrows and both coordinate laws explicit. Its concrete inputs
are the original inverse-image unit, skyscraper unit, right-adjoint
comparison, product projection, pulled-back-point projection, and geometric
germ. This avoids reconstructing the concrete stalk underneath product
projections. The final natural-isomorphism hom is still literally `stalkUnit`.

Run `remote-9f4b9afd86444d30b10df5c6db78f100`, source
`4aa83877118ceed0c631490c01354f8c01c426e2b13a99de184fc48abc6fbe97`,
accepted Projection and InverseImage in 3.213 and 7.254 seconds, reusing the
unchanged Skyscraper output. Total build wall was 15.444 seconds with peak
wrapper RSS 2663747584 bytes. These changed-source observations are not a
matched benchmark and do not isolate one optimizer cause. The canonical
maps, universes, hypotheses and resource budgets remain unchanged.

## Cancel the original unit before supplying concrete section rings

The first `Scheme.ArtinSchreier.rootOpen_appTop_root` proof in
[KernelCover](../Aglib/AlgebraicGeometry/EtaleCohomology/ArtinSchreier/KernelCover.lean)
mapped the original equation `e_i * b = i.val * e_i` through
`U_i.ι.appTop.hom`, cancelled the restricted idempotent unit, and simplified
the multiplication and natural casts in the concrete section rings.
At Lean 4.34.1 and the pinned Mathlib revision, run
`remote-32232dd2146848e1ba4d655ad98a274b`, source
`e7ecf61bc6628ee7ad781c6dd9c997db73b20420158791c19e05866f13aa79b6`,
exhausted 200000 heartbeats at `whnf` in that final theorem. Earlier declarations
had no diagnostics, but this failed invocation supplied no accepted module
artifact.

The retained private `map_eq_natCast_of_unit_factor` proves the same cancellation
over variable commutative rings, with a fully typed `RingHom`, original factor,
original root, natural number, mapped-unit proof, and original product equation
as explicit inputs. The geometric theorem then supplies the actual rings
`Γ(X, ⊤)` and `Γ(U_i.toScheme, ⊤)` and the literal `U_i.ι.appTop.hom`.
The original cover, unit, restriction map, public equation and mathematical
hypotheses are preserved, including the empty-scheme case.

Run `remote-3cbd553cb8a54250bb5bbaf0a8853ef3`, source
`8be7fe3ea0623ffa7ec897114394ce3989cf43e16abe0a122cdab1d2f4f8e50a`,
accepted the exact KernelCover leaf in 3.7 seconds with no diagnostics and the
standard heartbeat budget. Native resource ceilings were unchanged. This
records a validated proof-boundary repair without isolating a compiler cause
or measuring a matched speedup. The actual Artin--Schreier short-exact consumer
subsequently compiled in `remote-fdafdc1ba6484130bfca42898e69d458`;
that consumer is outside the leaf-only timing claim.


## Normal constants: typed Kan-extension comparison

Typed Kan-extension comparison for the original generic unit

Affected declaration
AlgebraicGeometry.Scheme.EtaleCohomology.NormalConstants.isIso_representedGenericUnit
in Constructible/NormalConstants/Represented.lean.
Lean 4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612;
private base 175a8ee20860f4ad7470cc3b043f618502380457.

Observed failed scope
remote-66083d8753994721b679a72634c53776, snapshot
5d168a61c59681d79109a8395e3a63841f6e8c4daa17a22f8e9f34245a5ab652,
Represented.lean SHA 0bb5d3986ed4b8454f8d3eb53d7d469934a5d81e0f9f7babdde960114998e363.
The concrete theorem transported the sheafification-unit isomorphism with
NatTrans.isIso_app_iff_of_iso applied to representedPresheafBaseChangeIso j H.
It exceeded the standard 200000 heartbeats at isDefEq, line 175:38, and the
whole declaration reported a whnf timeout. The run did not accept the module.

Validated repair
A private theorem isIso_unit_of_leftKanIso takes variable source/target schemes,
coefficient sheaves, a typed native Lan comparison iso, the actual restriction
arrow, its original factorization equation, and invertibility of that arrow.
Cancellation and the sheafification step stay inside this variable-map theorem.
The latter step transports Presheaf.IsSheaf through the comparison and applies
isIso_toSheafify, instead of transporting the natural-transformation component
at the fully expanded concrete Kan extension. The concrete represented theorem
supplies exactly representedPresheafBaseChangeIso, representedBaseChangeUnit and
the native descOfIsLeftKanExtension_fac equation. No map, hypothesis, resource
ceiling or mathematical statement changed.

Actual successful scope
remote-564eb185f0af40438bea720bf0a3e23b, snapshot
b63b61c86b7615e38a8191bc30b28bdef649f1f0ba58c402933a2255a376558a,
accepted the exact Represented leaf, SHA
7203bf4f2258ad998327f9d1be05372b08bcc99fbd3c9f8b246abccd92a2adad,
in a reported 15 seconds, with no diagnostics in that leaf, at 200000 heartbeats.
The same run failed in the root NormalConstants leaf on unrelated style and
instance lookup; it is successful evidence only for Represented. The final
root consumer subsequently compiled in remote-91552d915c764abd8454c7c6b4be047d,
snapshot 75bfa8baf56185dc212317b1065358c550058c385ccd014f11e5a1ffd9372524:
one fresh root frontend, exit 0, no diagnostics, reported 6.3 seconds.
The accepted Represented artifact was retained; it was not rebuilt.

This validates a proof-representation boundary. It does not isolate a compiler
cause or establish a matched speedup. No profiling, replay or benchmark was run.
Logs are retained under the adjacent remote-runs/<run-id>/build.log paths.


## Ringed coefficient equivalence: typed adjunction unit boundary


On Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, directly constructing the equivalence between the full subcategory of already-abelian-sheaf module presheaves and native ringed module sheaves exhausted the standard 200000 elaborator heartbeats at `whnf`. The failed declaration specialized the final triangle identity directly to `PresheafOfModules.sheafificationAdjunction α`. Its actual premise was a locally bijective map `α : R₀ ⟶ R.obj`, with native abelian sheafification and `WEqualsLocallyBijective`; the source objects had their actual original underlying presheaves already satisfying the sheaf condition.

The retained repair keeps the actual functors and adjunction as typed parameters of `equivalenceOfSheafAdjunction`. A separately typed `adjunctionUnitIso` names both full-subcategory objects before constructing the iso from the original `adj.unit.app`. Its component equation `adjunctionUnitIso_hom_app_hom` retains exactly that original arrow. The generic triangle proof first changes to the original `L.map (adj.unit.app ...)` composite, rewrites the typed component equation, and applies the original `adj.left_triangle_components`. The concrete definition then supplies the native module-sheafification adjunction, its already-proved actual unit-isomorphism supplier, and the native invertible counit. There is no additional public premise at the concrete equivalence or final standard-site endpoint, no alternative unit/counit, and no heartbeat change.

Failed concrete assembly: `remote-8144e600971340389df971c845ce4c50`, source digest `622dac5562656cfe941797358293f71eac1c1a6e3a051fc56d7466a0048f6fa9`; the Equivalence source hash was `4f9230f36a6b6cb011ef526d570f3845c5ac661c0c9e92542100da86a8d8fda6`. That invocation accepted the separate ConstantRing/Presheaf leaves and failed Equivalence after the reported `whnf` exhaustion; its later generated placeholder diagnostics were cascading failures, not authored `sorry` proofs.

Successful complete Equivalence provider: `remote-9454bb315c834f69ac20961def3f4d17`, source digest `0dfacbbd6d04be34c8461a883dd736d68494012ae8eae9d0c9597d321361c055`, owned Equivalence hash `a2ecd5fb8d36688a9907354fd752ed90eee02a2a047c459e6c8c3508b41e50f4`, accepted in 8.7 seconds. This run still failed the final Ringed root solely for missing local installation of the already-proved ring-unit local-bijectivity instances. The provider success is not a claim that the entire invocation or then-current root succeeded.

All original module/sheaf functors, scalar RingEquiv, constant-ring maps and abelian comparisons were retained. Native compiler evidence is preserved under `/Users/kang/Documents/New project/tmp/output/etale-amitsur-20261023/remote-runs/`. These are existing failed/successful proof-iteration observations, not a controlled benchmark or compiler-defect diagnosis; no extra run was launched for this note.

The standard root subsequently exposed a separate inference boundary: installing generic local-instance attributes, and then globally typed standard unit instances, still left the generic module-sheafification equivalence unable to match its inferred ring-unit map. The failed root-only run `remote-11390e5299ef4fa1b232058eb51e3c04`, global source `ab8899fe3d3ffa47b71da232e1b7bed7e4803ded916c1ed0b351f6d62419f91f`, root hash `5a00ea7bae67754f3c0d4df6f34eb51148f88a13c3ba531ceb36dde02672117a`, reported that missing instance and a downstream associator source mismatch. The retained root instead fixes `R₀`, `R`, and `α : R₀ ⟶ R.obj` as typed local constants equal to the original constant presheaf, associated ring sheaf, and original ring unit. It installs the existing proved local-injectivity and local-surjectivity as local constants at exactly that arrow, and calls the generic equivalence and its underlying comparison with named `R₀`, `R`, and `α`, letting their universes be inferred from the actual objects. Public `moduleEquivalenceStandard` and `moduleUnderlyingIsoStandard` record this concrete boundary; the final standard equivalence and original-ab-elian comparison consume them. This does not identify a Lean defect or prove that a particular universe-instantiation mechanism was the cause; it records the narrow successful elaboration boundary.

Successful final root: `remote-20fc45647d51488e8eeb931d17a102e6`, global source `0060ec8b72e3130a7969f4b395425b6f30632c36c19e163b3130e6b06b0476fa`, exact root hash `e807bdbd01c80c1a97bb327b6bae7bcb3d39a9830e9d0ac979a3a5ae4f5fd9c2`, one actual frontend accepted in 17 seconds, exit zero, no diagnostics, process group closed, with the three exact already-compiled lower sources retained. This completed the assigned four-source root closure without any change to its public mathematical conditions or the standard heartbeat budget. No further compiler invocation was made for this note.\n

### Transport additive presheaves before specializing geometric sections

On Lean 4.34.1 with the pinned Mathlib, constructing the actual quasi-coherent
[additive sections](../Aglib/AlgebraicGeometry/EtaleCohomology/QuasiCoherent/AdditiveSections.lean)
functor laws and forgetful sheaf proof directly across concrete
pullback/global-section carriers exhausted the standard 200000 heartbeats at
`whnf`. The earlier integrated source `22522f79b04a8d403056a0c4ad9b832d263fe985d9de809a6526a9ca1d20c853`
failed at those conversions in `remote-d4fb8ee110b84197a98f09b5b0e91954`;
subsequent unknown identifiers and generated-placeholder errors were cascading
compiler errors.

The retained repair proves additive transport and descent for a typed
presheaf, additive carriers, section equivalences and restriction maps in
[AdditiveTransport](../Aglib/AlgebraicGeometry/EtaleCohomology/QuasiCoherent/AdditiveTransport.lean).
The geometric specialization supplies the original Hom-to-section comparison
only after the functor laws have been proved. The opaque original restriction
map remains in `sectionsAddHom`, with its transport equation exposed by a
separate typed lemma. The forgetful sheaf criterion also fixes its original
object, morphism and value universes. Section groups, restriction maps and
scalar rings are unchanged.

The repaired producer `f97f0435481a507f36b7950f6b85df5e6bb6f89756580f986572ff55d0a0fce0`
compiled in 41 seconds in `remote-7cd592aabe864e869c3646647ae1e8fb`, source
`2bd9c76b74955775989dd37c8bfaf7ea5caa84227055f906b709e8f76f035190`,
at the unchanged budget. This is a per-module success; the same larger graph
has independent failing leaves. These existing proof-iteration observations
validate the transport boundary, without a timing comparison or an additional
benchmark run.


### Separate original-cohomology transport from concrete module injectives

For genuine `ZMod n` module sheaves,
[Cohomology](../Aglib/CategoryTheory/Sites/Torsion/ZMod/Cohomology.lean)
transports native ringed-module injective acyclicity to the original underlying
abelian sheaf. Combining the elementary subsingleton transport with concrete
Ringed-equivalence and `Sheaf.functorH.mapIso` objects exhausted 200000
heartbeats at `whnf` in `remote-03a4f5dae65b4c1a9d29d1072d512bc1`.
A broader equivalence/functor boundary still exhausted that limit in
`remote-1c16e566b50845fe8da0277353163f5c`.

The repair separates a pure typed additive-isomorphism transport,
`subsingleton_of_additiveIso`, from the original-H comparison
`cohomology_subsingleton_of_iso`, the native ringed-module acyclicity
application, and the concrete equivalence assembly. The H comparison names
its exact Ext universe and passes the actual source subsingleton witness
explicitly. The pure transport lemma has no over-category finite-products
premise; that premise remains at its genuine native acyclicity consumer.
The original coefficient equivalence, underlying-sheaf isomorphism and
cohomology maps are retained. No assumption of injectivity after forgetting
coefficients or increased search budget is introduced.

The final generic source `8720fa67ec3bfa720cd805487f6cc9a1b30fe50dde09df53e50a983b3ec8e21a`
and scheme adapter `7b77bb6787ba26f0c328df6f96094fb0ca54514e4cc9d2c007c45d903774004e`
both compiled in the isolated run `remote-c99b4ebc8371466a99c972dbb119499e`,
with two successful frontends and no diagnostics. Their native integration
frontends also succeeded in `remote-92d6f1ff4cf44a73affe4bbbccf68fba`
(35 and 14 seconds); that larger graph failed two independent scheme leaves.
These existing proof iterations validate the boundary, not a controlled
speedup or compiler-defect diagnosis. No additional run was made for this note.


### Build root-coordinate isomorphisms at variable sheaves

The concrete component construction in
[EtaleSliceRoots](../Aglib/AlgebraicGeometry/EtaleCohomology/Kummer/EtaleSliceRoots.lean)
exhausted 200000 heartbeats at `whnf` in
`remote-92d6f1ff4cf44a73affe4bbbccf68fba`, after the explicit projection from
roots of unity to units had repaired the earlier coercion mismatch.

The retained construction first builds a sheaf isomorphism for variable
sheaves, additive coordinate groups and coordinate equivalences. Its
components are exactly `eQ.symm ∘ eP`. The original roots-section naturality
is proved separately on two arbitrary coordinates, then supplied to this
constructor. Concrete inverse-equivalence terms are not expanded inside the
naturality calculation. The roots, unit restrictions, universe ranges and
absence of a modulus restriction are unchanged.

The exposed public isomorphism also needs both its constructor and its
naturality supplier accessible in the public context. The intermediate
private-helper versions reported explicit visibility errors; making those
two helpers public, with documentation, preserved their bodies. The final
source `a33d07879ab13e903334c440e59ef3a5cf7f76a435701367cb495c811273dc76`
compiled in 15 seconds in `remote-35548bdf7c4645d1884dbef6eff0c3f3` at the
standard budget. That run later failed the linter adapter, independently of
this successful source compilation, and passed the pinned production axiom
audit. No additional compiler run was made for this note.

### Stage affine scalar conversion before concrete pullback modules

In [AffineRestriction](../Aglib/AlgebraicGeometry/EtaleCohomology/QuasiCoherent/AffineRestriction.lean),
the actual `affineΓFunctor` functor carries a scalar action transported through
`isoSpec`; this action is not definitionally the literal top-section action.
The canonical `affineTildeΓRightIso` comparison identifies those actions
and is the identity on underlying sections. Applying this comparison inside
the concrete pullback-module tensor proof still exhausted 200000 heartbeats
at `whnf`, line 108, in `remote-5b024fda1c7a4eac86a929514b871a0e`, source
`302085fc5d909a2e179056ed01d91eac9ec2ab7971594c02cc8d9bc911699a68`.
The following unknown-constant diagnostic was cascading.

The repair moves this linear-comparison composition into
`affine_tmul_of_unit`, parameterized by an arbitrary affine scheme, source
module, target module sheaf, linear map and its unit equation. Scalar
conversion is checked before specializing to the pullback sheaf. The public
theorem then supplies the original `affinePullbackSectionsIso` and its
original `1 tensor m` equation. Separate typed function calculations retain
the original geometric unit composition and final restriction formula.
All three public statements, native scalar action, universes, affine and
quasi-coherence hypotheses remain unchanged.

The repaired source `823cefeda057714bba495b7ac7bd78ba0dc35fffce5b75abf209fdd12e44197a`
compiled in 20 seconds in `remote-b4d289d6f9e64987b48f6017cdc4e1bf`, global
source `fb3042f7b0743e75a8aca09370d3f36d3683123e8d2f0a815ce6c4425569ad51`,
at the unchanged budget. The larger graph failed only the independent roots
helper visibility. These existing iterations validate the staging repair,
without isolating a compiler cause or establishing a timing comparison.

## Hilbert-scheme naturality: rfl value lemmas and regular components

On 2026-10-19 the naturality proofs for the Grassmannian point of a Hilbert family
(`HilbertScheme/Naturality.lean`) were profiled in scratch copies of that leaf with
`set_option profiler true` and `profiler.threshold` 400 ms (200 ms for the last measurement).
The profiler outputs were not retained. The measured kernel times:

1. Rewriting with the composite equivalence, `rw [unitTwistH0Equiv]` followed by
   `simp only [LinearEquiv.trans_apply]`, cost 11.9 s. The `rfl` value lemma
   `unitTwistH0Equiv_apply`, used through `congrArg … |>.trans`, cost 0.24 s. The cause of the
   first cost was not diagnosed.
2. The naturality theorem instantiated at concrete bases cost 7.9 s. Proved once through an
   `rfl` lemma at a variable base `B` and used twice, it cost 3.2 s. From these two numbers,
   unfolding `grassmannianFunctorPoint` costs about 3.5 s per occurrence; this figure is derived,
   not measured directly.
3. Checking the `naturality` field of the natural transformation inline against
   `grassmannianFunctorPoint` cost 14 to 15 s, both through the `algSpec` presentation and with a
   directly defined functor, so the presentation made no difference. With the component as a
   regular definition and its naturality as a lemma stated through that definition, the check
   fell below the 0.2 s threshold.

Candidate mechanism for facts 2 and 3: lazy delta reduction unfolds the higher-height
`grassmannianFunctorPoint` first. This is the case "A structure field compared through its
unfolded statement" above, and the method "Preserve useful regular definition boundaries".

State the values of composite equivalences as `rfl` lemmas at variable arguments and use them
through `congrArg` and `trans`. Give the components of a natural transformation regular
definitions, and prove naturality as separate lemmas stated through them.


## Picard pullback: parameterize the target unit before specializing

At Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`,
the concrete scalar-frame rewrite in
[Picard.Pullback](../Aglib/AlgebraicGeometry/EtaleCohomology/Picard/Pullback.lean)
failed with an implicit-transparency `@Etale`/`MorphismProperty` mismatch.
The selected-build observation is `picard-kummer-02.log`, line 95 of that
failed source; no failed-source digest is asserted.

Use a completely abstract scalar/frame helper with the schemes, arrows, frame,
and both source and target units explicit. Take equality with the pulled-back
source unit as an input, then instantiate once with the original
`gmUnit_sections` equation. The retained `pullbackFrame_scalar_of_eq` helper
preserves the actual `gmUnit` and frame-torsor square; it does not replace the
coefficient morphism by another comparison.

The repaired leaf, source SHA256
`4c17ce8e264be91543524d3d9fed753e3253c33c21105474ab1fa74672098bc8`,
passed in 54 seconds in the existing `picard-kummer-03.log` observation with
the unchanged standard 200000-heartbeat budget. This validates that leaf's
repair only, not the later boundary-naturality, quotient or henselian
consumers. These observations are not a matched performance benchmark, and
no separate probe or resource-budget increase was added.

## Transport section equivalences before specializing the QC pseudofunctor

At the same Lean/Mathlib pins, constructing `NatIso.ofComponents` directly on
the concrete QC pseudofunctor Hom/section equivalence in
[SectionsNaturality](../Aglib/AlgebraicGeometry/EtaleCohomology/QuasiCoherent/SectionsNaturality.lean)
exhausted the standard 200000-heartbeat budget at `whnf`.
The existing observation is `qc-coefficients-02.log`, line 38:67, after 17 seconds.

Define `transportTypeFunctor` and `transportTypeFunctorIso` for an arbitrary
Type-valued functor and objectwise equivalences. Instantiate that abstract
natural isomorphism once at the native `homPresheaf` and `sectionsEquiv`.
This retains the original presheaf, actual sections of the pulled-back module,
restriction maps, and fpqc/fppf sheaf interfaces.

The exact repaired leaf, SHA256
`fdb58c9f5aac9efb149e2fee9b3ea21f8416fa0f15ceab627dcd992ad43b7dca`,
passed in 2.9 seconds in `qc-coefficients-04.log` without a budget increase.
This is an existing successful compile observation, not a controlled benchmark.
The separate SectionUnit, SectionsRestriction, EtaleSections and AmitsurProducts
consumer failures in that invocation are excluded from the success claim.

The same principle also applies to
[SectionsRestriction](../Aglib/AlgebraicGeometry/EtaleCohomology/QuasiCoherent/SectionsRestriction.lean).
Its concrete `mapComp` rewrite exhausted 200000 heartbeats at `whnf`
(`qc-coefficients-06.log`, line 48; 99 seconds). The abstract
`nativePullHom_eq` helper first pastes the existing component equalities with
`congrArg₂`, then specializes to the QC objects. The repaired leaf, SHA256
`a69299432bc13eb992c6d7a5692ceedab0575bb49a7b8a6e10e71b3d4c76ec2d`,
passed in 118 seconds in `qc-coefficients-07.log` at the unchanged budget.
This eliminated that heartbeat failure; it is not a wall-time speedup claim.
Original pullback/pushforward units and `pullbackComp`/`pullbackCongr` maps are
retained. The separate additive-coefficient consumer was still under repair.

### Stage subtype equalities before concrete matrix equivalences

In the actual crossed-product
[coefficient equivalence](../Aglib/FieldTheory/Brauer/CrossedProduct/Coefficients.lean),
a one-term `Subtype.ext (fromCoefficients_row hc h₁ x.property)` exhausted
200000 heartbeats at `whnf` (`brauer-cocycles-01.log`, line 94:29).
The repair explicitly types the full-indexed matrix in `toFun`, applies
`Subtype.ext` first, changes the goal to the original matrix equality, and
then applies `fromCoefficients_row` with the original membership proof.
The right-inverse proof similarly uses `funext`, an explicit `change`, and
the actual row identity instead of asking elaboration to discover all carrier
conversions inside one term.

The complete repaired producer, SHA256
`b67ae05a1e98a43e65686bd3748e4a3198add570329386462e26567e5e19b81f`,
passed in 3.7 seconds in `brauer-cocycles-03.log` at the unchanged native
200000-heartbeat budget. The intermediate graph 02 removed the first timeout
but still had a right-inverse error; only graph 03 establishes acceptance.
This validates the typed-staging repair, not a controlled timing comparison
or acceptance of the downstream centrality/simplicity/primitive producers.

### Transport complete additive naturality before specializing geometric sections

The additive transport boundary must include naturality, not only the component constructors.
In `qc-coefficients-26.log`, the final
[unit structure comparison](../Aglib/AlgebraicGeometry/EtaleCohomology/QuasiCoherent/StructureComparison.lean)
`NatIso` still exhausted 200000 heartbeats at `whnf` after individual lifted
additive components had been abstracted. The repaired `liftTransportNativeIso`
in `AdditiveTransport` proves the entire naturality square over arbitrary
`P`, `A`, `e`, `r` and the native additive target `Q`, before specializing to
scheme sections. The concrete `unitSectionsAddEquiv` and its actual native
unit-section naturality theorem remain unchanged.

The full StructureComparison producer, SHA256
`7760ceaf3f01c3048fb4ea2b08c9a2b12e3ac4985ba087de06dde1832534dce3`,
passed in 12 seconds in `qc-coefficients-28.log`; AdditiveTransport, SHA256
`ac88e351a741f7986b78b76ccbe28fa40262693994ad9384c087731cd0d85722`,
passed in 4.6 seconds, with the unchanged native budget. These are acceptance
observations, not a controlled speedup or acceptance of CoefficientMaps,
BaseRestrictionAdditive, or the downstream cohomology comparison.

For base restriction the analogous full-boundary repair is
`liftTransportIsoOfTypeIso`: prove the Type-natural-isomorphism-to-additive
transport abstractly, then supply `sectionsBaseRestrictionIso` and the named
component evaluation equality. This retains the original `pullbackComp`
components. The concrete section-naturality specialization in
`qc-coefficients-30.log` exhausted 200000 heartbeats at `whnf` (49-second leaf).
BaseRestrictionAdditive, SHA256
`9a70f8e1fd1be4bc88aa422d1ad4a94f6954f9b9b356f33ca4d8eb1452f3a6ba`,
passed in 38 seconds in `qc-coefficients-32.log`; the expanded AdditiveTransport,
SHA256 `c53d9228e314117d956f3f81453399d8683594bd596a3fe589ad3855bfe6f6a6`,
passed in 5 seconds. Budgets were unchanged. This validates that boundary,
not a controlled timing comparison or the pending coefficient-map/Amitsur consumers.

For maps on the same site, also absorb the identity functor and left unitor
inside the abstract transport helper. The concrete `liftTransportHom`
specialization in `CoefficientMaps` still exhausted 200000 heartbeats at `whnf`
in `qc-coefficients-31.log`. `liftTransportHomSame` checks that complete
same-site construction before geometric specialization, retaining the actual
`coefficientSectionsAddHom` and original coefficient naturality. After ordinary
identity/composition normalization in graph 32, CoefficientMaps, SHA256
`b4e0e2250ce17e33e507c15900aee7ba6661c109f339facf0c3010191cbc416a`,
passed in 12 seconds in `qc-coefficients-33.log`, with no budget increase or
separate benchmark.

The original Amitsur-to-Cech transport needs the same full boundary for
opposition and whiskering. In `qc-coefficients-39.log`, the concrete
opposite-diagram isomorphism/section-whiskering conversion exhausted 200000
heartbeats at `whnf` (21-second failed leaf). Generic `rightOpSectionsIso`
checks the inverse identities and functor-composition conversion before any
scheme/module specialization. The original geometric isomorphism, coefficient
and `amitsurCechSectionsIso` interface are retained. AmitsurCech, SHA256
`6f10c40dc35b0d57761531f980fc4b26fd6389c752c7a4245bc528fbcc3a4d5a`,
passed in 3.3 seconds in `qc-coefficients-40.log` with the same budget; this is
acceptance evidence, not a controlled speedup or a Zariski-consumer acceptance.

For the final original Zariski module-coefficient naturality square,
`qc-zariski-06.log` hit maximum recursion depth in one `change` computing
sheaf-preimage, open inclusion, transport and `ULift.down` simultaneously
(7-second failed leaf). The repair first proves `zariskiModuleIso_hom_app`
at the bundled-morphism level, retaining the opaque original presheaf iso
and using only the actual identity/map-identity equations. Consumers rewrite
that named equality before evaluating `down` by `rfl`. The original component
formula and coefficient naturality are unchanged. ZariskiModuleCoefficients,
SHA256 `adf2847e95382b4fee2adf79dd7e89023b664ba43b0729c85517aa67a0aef6e5`,
passed in 16 seconds in `qc-modules-01.log`. No recursion/heartbeat limit was
raised, no benchmark added, and downstream original-H wrappers were not part
of that acceptance.

### Fix site objects before applying a generic finite-sum descent theorem

The finite-etale trace gluing producer exhausted 200000 heartbeats in
`isDefEq` at `chartSum_independent` in `finite-trace-08.log`: the target of the
chart morphism was still unresolved during specialization. Supplying the
actual `(X := X)`, `(V := V)` and `(U := (toEtale X).obj Y)` to the existing
generic independence theorem removed that timeout in graph 09. Graph 09 still
had unrelated projection/linter diagnostics; only `finite-trace-10.log`
accepted the complete Gluing producer (6.1 seconds), SHA256
`ff0fe364e1fe5f53cf507d3f48f560e110bb2cf7afe18308bd34e78c3688c915`.
No budget increase or separate timing experiment was used. The original sums,
local transition maps and finite-flat rank equation remain unchanged; this
receipt does not certify the downstream normalized trace/source square.

### Specialize a complete coproduct projection identity, not its intermediate rewrites

The actual generic-Artin pullback point-index producer repeatedly failed to
normalize the projection through `pullback (Sigma.desc ...)` versus
`pullback (genericArtinMap X)`. In `generic-discrete-09.log`, even the requested
`Category.assoc` rewrite did not match across that wrapper. This was an
elaboration/normalization failure, not evidence of a resource timeout.
Prove the entire first-projection identity for an arbitrary literal family of
schemes and maps; only then specialize the completed identity to the original
generic-Artin map with `exact`. The native Sigma inclusions, pullback symmetry,
finite-coproduct comparison and literal projection equation are unchanged.
GenericArtinBaseChangeIndex, SHA256
`89edc71d5f135c1679a4e90c712f3a507066dd5985d911c4b53acc430d3309be`,
passed in 4.9 seconds in `generic-discrete-10.log`. No budget increase or
separate benchmark was used; the receipt does not validate later support
consumers.

### Pin the existing Ext universe before specializing a concrete fibre

In `root-b3-03.log`, the final characteristic-primary restriction wrapper hit
the 20000 typeclass-synthesis heartbeat limit trying to reconstruct `HasExt`
through the local `Over.left C` abbreviation. The original target fibre already
had the required `HasExt` instance. Install that exact instance on `C.left` with
`inferInstanceAs`, then apply the accepted vanishing theorem with its explicit
Ext universe. Also rewrite the chosen degree equality rather than letting
`subst` pick a differently oriented arithmetic equality. No new cohomology
model, universe equality assumption or budget increase is needed.
CharacteristicPrimaryRestriction, SHA256
`69df63d03c2623e63892604a19155528a2046f355442e94e061bd64cb3988fae`,
passed in 35 seconds in `root-b3-04.log`. This acceptance is the actual
characteristic-primary original restriction endpoint, not the remaining
prime-to-characteristic curve branch.

### Type the original Hom endpoints before expanding an adjunction composite

`finite-trace-14.log` exhausted the standard 200000 heartbeats in `whnf` while
evaluating the composed adjunction for the finite-etale source comparison
through concrete small-etale wrappers. Fix the full Hom type first, from the
actual slice integer coefficient to `inverse.obj A`; compose typed
`congrArg`/`trans` identities rather than rewriting beneath unresolved
adjunction wrappers. Select the original slice exactness instance explicitly,
`overPullback_preservesFiniteColimits.{u+1,u,u+1}`, where universes are otherwise
underconstrained. The source and target Ext universes remain independent.
SlicePullback.SourceSquare, SHA256
`3e2b3330ec34033a7f5beec764a756150a55104949d20c93349c5c2595b5637d`,
passed in 69 seconds in `finite-trace-16.log` without raising any budget.
This validates the literal original pullback/source square, not the later
finite-field scalar-transfer injectivity consumer.

The same explicit-Ext pattern applies to original field pullback effacement.
In `field-dimension-04.log`, `PullbackEffacement` reached the native 20000
instance-search limit while reconstructing `HasExt` through
`(Functor.fromPUnit X).obj U.right` and the finite-field-cover chart wrapper.
Fix `(X := X)` and `(S := U.left)`, then transport the existing chart `HasExt`
with `inferInstanceAs`; do not ask typeclass search to rediscover it beneath
the geometric wrapper. The next graph's ordinary `map_zero` rewrite failure
was separate: under implicit transparency, the unfolded `@Etale` property did
not match its bundled `MorphismProperty`. Typed additive-equivalence aliases
and complete `congrArg`/`Eq.trans`/`map_zero` identities avoid rewriting there.
PullbackEffacement, SHA256
`45f19c79c2a7a9d194e968b34df0410ab12c85c7ea323866d0ae4bf62b79fb5e`,
passed in 37 seconds in `field-dimension-06.log`; its original dimension-shift
consumer passed in 26 seconds. These are acceptance receipts, not a controlled
speedup measurement. Original maps, independent Ext universes and all budgets
are unchanged; the geometric finite-coinduction and H2 inputs are separate
suppliers, not certified by this consumer graph.

### Stage pointed fibre identities before specializing field restriction

In the field-restriction graph, specializing the entire pointed precomposition
identity at the native field chart made elaboration and kernel checking unfold
large concrete fibre and Galois constructions. `field-sylow-10.log` recorded a
kernel deterministic timeout (97 seconds); `field-sylow-11.log` and
`field-sylow-12.log` reached the unchanged 200000 weak-head-normalization budget
(35 and 21 seconds). These are distinct failure receipts, not benchmarks.

Prove the fibre-component identity first with an abstract typed scheme map,
pointed fibre and cover. Derive the pointed-map identity from that statement,
then specialize to the native field map in a separate opaque theorem. The
accepted staging uses `pointEnd_left_restrictScalars`,
`pointedFiber_toFibreAut`, `pointedMap_toFibreAut_of_map`, and finally the
canonical field/Galois comparison. Explicit source, target and scheme
parameters keep instance reconstruction out of the concrete final application.
`Field.Restriction`, SHA256
`322ddfbd7a75809a1a603807f9b838c0057789c88665c6ef4f14c825fff13e71`,
passed in 4.3 seconds in `field-sylow-13.log`, without increasing any budget.
This certifies the original restriction comparison only; the subsequent Sylow
and finite-coefficient H2 theorems require their own acceptance receipts.

A separate kernel-memory failure occurred in `SylowMonodromy` at line35:8
in `field-sylow-17.log` (83 seconds): elaboration had completed, but the concrete
native fibre-equivalence power transport exceeded the unchanged memory limit.
Extract the entire conjugation through `autEmbedding` and the fibre equivalence
into `FundamentalGroup.PointedPower.component_pow_eq_one_of_pointedMap`, with
the actual pointed map, automorphism, cover and exponent abstract. The concrete
field theorem then uses the component identity and one opaque application.
The proof still uses the original pointed maps and field restriction data.
In `field-sylow-18.log`, PointedPower (SHA256
`e880022d25300827ed32462e7314458b22ad0ec4969fac6e2032349580fa5c90`)
and SylowMonodromy (SHA256
`a5d9c9668b032868713461900c696820d9134da2ee474aeb4c93bbaa1f559556`)
passed in 2.9 and4.6 seconds. The graph then failed in the downstream SylowLine
consumer. These local receipts do not certify that consumer or the finite-H2
endpoint, and no resource ceilings were increased.

### Use native sized subobject infima instead of rebuilding a concrete lattice

For the actual point-supported subobject of an original abelian etale sheaf,
complete-lattice inference reached the unchanged 20000 typeclass budget in
`generic-support-06.log` (130 seconds). A later explicit lattice still made the
concrete infimum bound normalize too much: `generic-support-11.log` reached
200000 weak-head-normalization steps (47 seconds).

Keep the native Grothendieck sheaf structure and express the same infimum as
explicitly sized `Subobject.sInf` of the range of the original kernel family.
Use native `sInf_le`/`le_sInf`, an abstract kernel-factorization relation, and
native downward AB5 for the actual point fibre. This avoids reconstructing an
unused concrete complete lattice; it does not assert that a fibre preserves
infinite infima. PointSupportedSubobject (SHA256
`0aee711895e260d4290840b065e3ddb3569e48a3a0f1c6da71ffe1e1a4518a15`)
passed in 4.3 seconds in `generic-support-13.log`, and the closed-unit consumer
passed in 2.6 seconds. Exhaustion and higher-cohomology consumers are separate
unaccepted targets at this checkpoint. No budgets were raised; these are
acceptance receipts rather than a controlled performance comparison.

The same explicit-Ext transport also resolved the actual generic higher-image
consumer. In `generic-higher-03.log`, GenericHigherImages at112:13 reached the
unchanged 20000 typeclass budget while reconstructing localized Hom smallness
on the literal pullback behind a chart wrapper (102 seconds). Install the
`HasExt.{u+2}` for that pullback with `inferInstanceAs` from the existing
`HasExt.{u+2}` on the chart's `T.left`, and specify the power theorem's
`.{u,u+2}` universes. GenericHigherImages (SHA256
`71feb1d19cd0d7b6b93fabc2bf024f80dbdc9883af98ee72650c66b74668baf4`)
passed in 66 seconds in `generic-higher-04.log`; its original direct-image
cohomology divisibility consumer passed in 7 seconds. These validate the
unchanged actual sheaves and maps, not a controlled speedup comparison.

## Original represented étale cohomology: normalize complete values before specialization

The initial `Stalk/OriginalCohomologyZero.lean` proof expanded the concrete
Ext-to-native-derived comparison inside the scheme sheaf category and hit the
unchanged 200000-heartbeat limit at `whnf` (native compilation graph005).
The first unit calculation also needed an explicit unfolding of only
`rightDerivedNatIso` so its hom matched the existing native transformation lemma.

The successful repair retained exactly the original Ext.mk₀ class, native
injective resolution, represented-section isomorphism, and degree-zero derived
unit. A private abstract `representedExtZero_of_eq` takes the complete additive
comparison E, original input class x, and output value y, together with their
canonical equations. It performs the Ext.mk₀ rewrite abstractly. The concrete
scheme theorem supplies the actual objects and maps with rfl witnesses instead
of asking the elaborator to reconstruct and normalize the full sheaf carriers.

Graph007 compiled the entire changed `OriginalCohomologyZero` leaf in 28 seconds.
No heartbeat limit increase, separate test, or kernel replay was used. The
accepted `OriginalCohomology` and `ResolutionPresheaf` providers were unchanged.
This is evidence for the degree-zero normalization repair, not acceptance of
unrelated site restriction naturality or the full higher-image stalk theorem.

## Small étale morphism-property boundaries: preserve typed native objects

The finite affine refinement producer failed in graphs001,004,006 and010 with
instance and implicit-transparency mismatches at the `Scheme.Etale` /
`MorphismProperty.Over` boundary. Printed morphism-property heads could look
identical while elaboration could not identify the expected native category.
Use the explicitly typed eta-expanded property
`fun {X Y : Scheme.{u}} (f : X ⟶ Y) => AlgebraicGeometry.Etale f`, and provide
the original-site category to constructors such as
`Presieve.ofArrows.mk (C := S.Etale)`. For a native Over factorization, typed
`congrArg` and `Eq.trans` avoid an unnecessary `calc` transitivity search through
projected carrier expressions. Reuse the actual covering and morphism-property
instances rather than inventing alternate site structures.

Graph014 accepted `EtaleAffineBasis.FiniteRefinement` in2.0 seconds and
`FiniteHypercovers` in2.2 seconds with these repairs. These are full-leaf native
build times, not isolated benchmarks. No heartbeat or linter relaxation, test,
audit or kernel replay was used. The later qcqs hypercover consumer remains a
separate compilation obligation.

## Typed projection proofs across additive Hom carriers

Evidence: the native FiniteFreeHom target failed in graphs 029 and 034, then passed in graph 036 (5.3 seconds). No additional benchmark was run.

When an additive equivalence on a raw Hom type is converted with `AddEquiv.toAddCommGrpIso`, downstream goals may present its source as the native preadditive Coyoneda `MShrink` carrier and its target as the concrete product cone point. These are definitionally compatible at full transparency but rewriting can reject the entire target as ill-typed at implicit transparency.

Do not repeatedly change equivalent projection rewrite lemmas. After the ordinary associativity and `Pi.isoLimit_hom_π` steps, compose the fully typed canonical projection equality using `congrArg`, not a further rewrite through the additive equivalence. Annotate BOTH objects of `toAddCommGrpIso` explicitly as `AddCommGrpCat.of ...`: otherwise a lambda elaboration leaves the source group as a metavariable (graph 034).

The successful proof uses `exact congrArg (fun f => (E.toAddCommGrpIso : AddCommGrpCat.of X ≅ AddCommGrpCat.of Y).hom ≫ f) (limit.conePointUniqueUpToIso_hom_comp hc j)`, with actual E, X, Y, hc and j supplied. The final generator evaluation is definitional. Keep any required existing backward-defeq options local to the theorem. This is a typed-term elaboration repair, not a reason to increase resource limits or run kernel replay.

## Short-complex colimit comparisons: normalize abstract endpoints first

On baseline3b4b58eb with pinned Lean4.34.1, native graphs041–046 failed while
rewriting preservation formulas that mixed `(T ⋙ π₁).obj X` and
`(T.obj X).X₁`. The target could not be checked at implicit transparency.
Local backward-transparency settings and `erw` did not resolve the final
mixed-composite match. Instead prove the preservation square for abstract
functors F,H and a natural transformation α, then instantiate α with the
native short-complex projection transformation using `exact`.

Graph049 accepted `Continuity.ShortComplexColimit` in1.3 seconds with this
repair, without extra transparency options or increased resource budgets.
This is full-leaf native evidence, not a benchmark or a kernel-defect claim.
No additional test, audit or kernel replay was used.

## Additive Ext transport: avoid an irrelevant integer-module diamond

Graph073 of ExactImageComparison.Cohomology, with pinned Lean4.34.1 and
Mathlib d13f23b, failed when converting `Ext.precompLinearEquiv ℤ` to an
additive equivalence: the inferred integer module on the native Ext carrier
was not definitionally equal to `AddCommGroup.toIntModule`. This scalar
structure is irrelevant to the additive cohomology endpoint and is not a
missing Ext-size instance.

Use the scalar-free `Ext.precompIsoAddEquiv`, built from original `Ext.precomp`
and the actual isomorphism and its inverse, with native Ext associativity.
Retain original `Adjunction.extEquiv`, cohomology pullback/counit and independent
source/target HasExt universes. Explicit associativity degrees0,q,0,q avoid
unresolved degree metavariables. Existing graph076 then accepted the complete
Cohomology leaf in60 seconds; Exact graph071 and Exchange graph073 were
unchanged. No additional benchmark, replay or budget change was used.

## Pullback Gamma coherence: transport typed identities explicitly

In Continuity.PullbackCohomologySystem, graphs078–080 could not simplify
identity maps inside inverse-image composite comparisons: composite.obj and
nested.obj left the native `map_id` and `id_comp` endpoints unmatched.
Keep the original comparison isomorphism and transport the typed `map_id`
and `Category.id_comp` equations with `congrArg` through its complete hom
and inv endpoints. Compose those equations using `Eq.trans`, finishing with
original `Iso.hom_inv_id_app`, rather than expanding the composite functor.
Graph082 accepted the complete leaf in40 seconds on the pinned Lean4.34.1
and Mathlib d13f23b baseline. No heartbeat, transparency or synthesis budget
was raised, and no extra benchmark or kernel replay was run.

## Finite pointed lifts: name the residue-point morphism

FiniteNeighborhoodLift graph076 exhausted the ordinary200000-heartbeat
budget while repeatedly elaborating residue Spec maps in the component
triangle. Name the original morphism `localComponentResidueMap`, with its
complete source and target, and explicitly type the MaximalSpectrum binder.
Prove the scheme triangle componentwise through coproduct injections and
transport the residue triangle using typed equations. Graph084 accepted
the complete leaf in2.6 seconds after ordinary proof and formatting fixes.
This records observed compilation evidence, not a standalone benchmark;
no resource budget was raised and no replay was used.

## Original cohomology squares: normalize the whole comparison first

CohomologySquare graphs079 and082 timed out during ordinary compilation
when reducing inverseImageSquareIso at concrete components. Normalize the
whole isomorphism chain first using the generic iso_comparison_square and
the native inverseImageSquareIso_comp_hom equation. Then use congr_app and
an additive element-transport lemma with explicit AddCommGrpCat.comp_apply
and typed Eq.trans, rather than unfolding the original sheaf carriers.
Graph084 accepted SquareComparison in2.7 seconds; graph085 accepted
SquareTransport in885 milliseconds and CohomologySquare in16 seconds.
The original maps and four independent Ext universes are retained, without
new mathematical premises, larger budgets, or additional replay/benchmarks.

## Chart Ext comparisons: abstract the complete values before specialization

ChartSourceMap graph093 exhausted200000 heartbeats at whnf while composing
concrete slice and chart Ext comparisons. A private generic twoStep_ext_of_eq
lemma first composes the complete Ext values and their already-proved
comparison equations in abstract categories. Specialize that lemma once,
with explicit original HasExt, additive and finite-colimit instances for
the local functor aliases, rather than rewriting through concrete carriers.
Graph097 accepted the full ChartSourceMap leaf in28 seconds after the alias
instances were supplied. The original maps and independent Ext universes
remain unchanged. No larger budget, extra test or kernel replay was used.

## Diagram inverse-image comparisons: type the transported morphism

DiagramPullbacks graph097 exhausted200000 heartbeats at isDefEq when an
untyped morphism variable in congrArg and an inferred Iso.trans midpoint
forced inference through the concrete inverse-image functors. Explicitly
type the scheme-op Hom domain and the intermediate isomorphism with the
original inverseImage source and target. This removed the timeout in099;
typed transport of the original mate equation completed graph101 in7.1
seconds. No transparency or resource option was changed.

## Inverse naturality of representative sections: use the original hom equation

RepresentativeSections graph106 exhausted200000 heartbeats at isDefEq when
specializing the inverse naturality of the full pullbackSectionsEtaleNatIso.
Use the accepted original pullbackSectionsMap_etaleEvaluation hom equation,
then cancel the two explicitly typed chart isomorphisms via inv_hom_id.
Graph108 accepted the entire leaf in92 seconds on baseline37cce7b, with no
budget or transparency change. This is successful ordinary compilation,
not evidence of a measured performance speedup or an extra test run.

## Horizontal base-change unit: prove whole mate equations abstractly

BaseChangeHorizontalUnit graph110 exhausted200000 heartbeats at isDefEq
while expanding a concrete scheme inverse-image conjugate chain; rewriting
the concrete base-change map also caused an ordinary compiler kernel timeout.
Prove the complete isomorphism-chain conjugation and horizontal unit equation
first for abstract categories, functors and adjunctions. Instantiate with the
original inverseImageComp, equality transports and existing conjugate
identities as complete proof terms, rather than rewriting inside their
concrete carriers. Graph114 accepted the full leaf in3.2 seconds, with the
same mathematical premises and resource budgets. No replay or separate
benchmark was performed.

## Canonical etale exchange: compare the whole continuous pushforward chain

EtaleDirectImageMate repeatedly exceeded the default kernel/isDefEq budget
when projecting a chain of direct-image composition and equality isomorphisms
onto concrete sheaf components. Individual component equations still forced
the kernel to normalize several large category carriers together.
Instead identify each original directImageComp hom/inv and equality transport
with its continuous-pushforward natural transformation at the whole functor
level. Compose there using a generic continuous-transformation chain lemma,
then evaluate only once. Supply the original composite-site continuity
instances explicitly. The final exchange proof uses the complete original
unit and site-square equations as typed inputs.
Graph127 accepted the full canonical EtaleDirectImageMate leaf in91 seconds
on37cce7b, without increased budgets or new mathematical premises. This closes
the original baseChangeMap identification, not merely existence of an iso.
The timing is ordinary compilation evidence, not a matched speedup claim.

## Affine-limit section equality: type the isoSpec arrows and section values

AffineSchemeSectionEquality exhausted the ordinary whnf heartbeat budget
while inferring concrete isoSpec arrows and cancelling their action on
original section values. Specify the original arrows hU/hV, and pass the
entire mapped isomorphism and all section values into a generic additive-
category equality lemma. Graph128 accepted the full leaf in3.8 seconds on
37cce7b without changing resource budgets or the original maps. This records
actual proof compilation; no separate replay or benchmark was performed.

## Finite chart stalk comparison: use explicit native isomorphisms

The monolithic GlobalEvaluationChart proof in graph129 exceeded the native
memory limit. Splitting the actual index, chart stalk comparison and coordinate
identity exposed a further kernel timeout in ChartStalkComparison graph130:
`asIso` of the stalk image of the canonical exchange required normalization of
its inferred IsIso instance and inverse.
Use the original nativeStalkIso.app and the explicit
sheafFiber.mapIso(etaleBaseChangeIso.app), then prove a complete hom boundary
using the original nativeStalkIso_hom and etaleBaseChangeIso_hom equations.
Graph131 accepted ChartStalkComparison in2.4 seconds, the coordinate leaf in
2.2 seconds and GlobalEvaluationChart in1.0 second. Memory/heartbeat ceilings,
mathematical hypotheses and canonical maps were unchanged. No extra replay,
audit or matched performance benchmark was run.

## Resized cohomology diagrams: stop extensionality at the actual group element

FibreProductPresheaf graph132 failed when `ext x` recursively invoked
`Shrink.ext`: the resulting goal had already been transported back into the
original Ext universe, so a subsequent `change` to an equality in the resized
group was not definitionally correct. Its natural-isomorphism proof also left
an unresolved `u + 1 = max w ?v` universe constraint for untyped Shrink maps.
Use `ConcreteCategory.ext_apply` explicitly to stop at the actual resized
group element. Give the source and target Shrink additive equivalences complete
types, and transport the original functor's whole identity equation using
`ConcreteCategory.congr_hom` and `congrArg` instead of implicit rewriting.
Graph135 accepted the full leaf in 219 seconds on 37cce7b, retaining independent
base/slice/scheme Ext universes and the original coefficient sheaves. This is
ordinary compilation evidence, not a speedup claim or evidence that inherited
elaborator transparency options are necessary. No budgets were increased and
no separate benchmark, audit or replay was performed.

## Relative section scalars: name the actual transport before evaluating

The finite representative consumers in graphs134–136 encountered kernel
normalization timeouts when instantiating a generic equality lemma with the
original chart-evaluation iso, the coefficient-composition map, and several
large abelian-group morphisms simultaneously. Replacing the two intermediate
maps by an inline composite still left the concrete carriers in that proof.

PullbackScalarTransport names the actual composite E.inv followed by the
original global-sections image of inverseImageComp.inv as a single typed
morphism. Its unit and restriction equations are separate opaque theorems;
separate scalar lemmas then evaluate one accepted equation at a time using
ConcreteCategory.congr_hom and the original composition-application equation.
Consumers can combine scalar equalities with congrArg and Eq.trans without
reconstructing the intermediate isomorphism or all the group carriers.
Graph138 accepted this complete supplier in 3.7 seconds on 37cce7b. At that
point the downstream scalar consumers were still awaiting compilation; this
entry does not claim that their independent timeouts were already resolved.
The original maps, hypotheses and resource budgets are unchanged. No extra
test, audit, kernel replay or comparative benchmark was run.
The next ordinary graph139 accepted the downstream FiniteSectionRepresentatives
consumer in 22 seconds and UnitSectionsAmalgamation in 2.7 seconds using these
scalar boundaries. This validates the finite-representative path specifically;
UnitRepresentativeEquality and SectionsCompatibility had not yet been accepted
in that graph and are not covered by this observation.

## Cohomology cone legs: specify the actual scheme endpoints

In graph139, `DiagramCohomologyCocone` inferred the target scheme of a cone
projection as `((Functor.const I).obj c.pt).obj i`. Searching for `HasExt`
on that expression expanded to localized-Hom instances and exhausted the
20,000 typeclass synthesis heartbeat limit. A later equality also reached
the separate 200,000 elaboration heartbeat limit; subsequent cocone errors
were cascading and were not evidence of a mathematical obstruction.

Specify the source stage scheme and the actual target `c.pt.unop` explicitly
in `cohomologyTransfer` and `cohomologyTransfer_triangle` applications. This
selects the existing `HasExt` instances without unfolding the constant diagram.
Keep the Ext universe independent of the scheme and coefficient universes.
For cocone naturality, compose the typed equation with `Category.comp_id`
rather than asking simplification to identify opaque cohomology objects.
Graph141 accepted the complete cocone leaf in 43 seconds on 37cce7b after
these changes and an ordinary `colimit.ι_desc` argument correction. No budget
or transparency option was changed; no extra benchmark, test, audit or kernel
replay was run. This records a validated repair, not a comparative speedup.

### Fixed pullback systems: compose transformations before evaluating coefficients

The fixed-coefficient inverse scheme system encountered kernel excessive-memory
failures in its native transition composition proof (compiler graphs 141 and
142). A separate concrete `congrArg` transporting the adjunction composition
comparison also reached the unchanged `whnf` limit. The generic mate constructor
and abstract scheme-triangle laws themselves were already accepted; the expensive
boundary was their simultaneous specialization to indexed scheme maps and an
actual sheaf coefficient.

In `EtaleCohomology/Stalk/PullbackCoefficientSystem.lean`, the successful repair
first proves the triangle composition as an equality of whole natural
transformations, specializes that equality to the diagram, and evaluates it at
the coefficient only once. `System.ofLeftMapsWithComparisons` transports the
specified identity and composition isomorphisms at the abstract adjunction
boundary, rather than constructing a large concrete component-level `congrArg`
inside the native system definition. The original inverse-image triangles and
adjunction comparisons are unchanged.

The exact repaired leaf passed the normal production build in graph 144 (97 s).
This is evidence of acceptance after the diagnosed failures, not a benchmark or
a claim that compilation is optimized. No limits, elaborator options, kernel
replay, or additional validation runs were introduced for this repair.

## Original tuple cochains: normalize typed carriers before transport

With Lean 4.34.1 and Mathlib d13f23b, graphs 142–151 of the continuity task
encountered implicit-transparency endpoint mismatches and 200000-heartbeat
`whnf` failures while rewriting native Hom-complex carriers and tuple-product
generators. Unannotated product vertices also forced unnecessary reduction of
chosen limit cones. No mathematical product-preservation assumption was missing.

Construct the degree maps first on the explicitly typed original Hom groups.
Use named original product objects, tuple generators and site arrows, and
transport the native chain-map and tuple-projection equalities by whole-value
`congrArg`. Evaluate the free-family Yoneda comparison through those typed
generators rather than unfolding the complete Hom complex during rewriting.
For dependent products of section equivalences, first map the actual abelian
isomorphism through `forget`, then use the native type isomorphism equivalence.

Graph 148 accepted `Continuity.TupleBaseChange` in 4.3 seconds; graph 152 accepted
generic `Continuity.FamilyBaseChange` in 5.1 seconds and its actual etale adapter
in 3.4 seconds. These are full-leaf native acceptance results, not benchmarks.
No budgets were raised and no extra tests, audits or kernel replay were run.
Only the additive Hom cochain comparison is proved invertible; the underlying
map of free tuple presheaves is not asserted to be an isomorphism.

The corresponding `Stalk/PullbackLimitCoefficient.lean` encountered the same
concrete-component expansion in its naturality proof (graph 146). Its accepted
repair also specializes a whole original triangle transformation before a single
coefficient evaluation. Explicit native endpoint isomorphisms avoid relying on
simp to identify constant-functor objects with the original sheaf objects. The
constant-diagram colimit insertion equation is proved in an abstract category,
with independent index and target object/morphism universes, then instantiated
without unfolding the concrete sheaf category. Proof helpers referenced by an
exposed definition must themselves be publicly accessible; merely putting the
construction in a tactic block does not remove that module visibility boundary.
The exact leaf passed graph 152 (67 s), with unchanged budgets and options. This
is acceptance evidence, not a benchmark or an additional validation cycle.

### Preserve native representative interfaces across geometric specialization

In the étale continuity implementation, a concrete matching proof repeatedly exceeded the
normal deterministic kernel budget even after its Scheme/Over geometry and abstract
functor algebra had been separated. The abstract helper consumed naked `P.map` values
and explicit evaluation-inverse seeds, whereas both the accepted input producer and
required conclusion used `etaleRepresentativeSection`. Specializing the helper therefore
forced simultaneous reduction of deep pullback-source objects, the original section
functor, and the evaluation-inverse endpoint types.

The successful repair keeps the native interface intact: prove equality transport for the
original coefficient sheaf and arbitrary Over objects, with
`etaleRepresentativeSection` on both sides and original coefficient sections as inputs.
Its proof uses the existing native restriction theorem. Specialize this theorem once to
the already-proved geometric arrows. Also align the geometric arrow's source and the
consumer statement with the literal native `Over.mk` source of `unitRepresentativeArrow`,
rather than requiring an additional source-object alias conversion under the section
functor. No replacement cohomology, extra mathematical assumption, increased budget,
or kernel replay is involved.

Normal compilation on 2026-10-23 accepted `BaseChangeUnitMatching` in 8.6 seconds and
its actual stage-sheaf amalgamation consumer in 2.5 seconds (graph157). These timings
validate this interface repair, not completion of the full scheme-limit continuity theorem.

## Reindexed direct-image comparisons: evaluate a whole identity first

The first `DiagramDirectImageTriangleComp` compilation in graph157 reached
the 200,000 elaboration heartbeat limit at the final `Category.assoc` transport.
The native scheme triangle lemmas had elaborated; the remaining problem was
implicit normalization of the reindexed adjunction comparison at a concrete
sheaf object.

Normalize that reindexed comparison first as an equality of whole natural
transformations (`diagramDirectImageComp_inv`), evaluate that equality at the
specified coefficient object, then use a `congrArg` with explicit source and
target to postcompose the original triangle. The final proof joins these typed
equations with the already established native associativity equation. Graph159
accepted the full leaf in 10 seconds on 37cce7b. Resource limits, original maps,
and hypotheses were unchanged; no separate benchmark, test, audit, or kernel
replay was run.

### Whole fixed-site cochain cocones before concrete geometric specialization

In graph162, `FamilyTailCochains` reached the kernel's normal memory guard while
checking a concrete sheaf-cochain colimit certificate. The proof supplied a
presheaf cocone mapped in two steps, whereas the actual consumer used the whole
sheaf-to-presheaf and additive Hom composite. Converting those cocones directly
expanded the concrete right-tail coefficient system and geometric site carriers.

Keep that conversion at the fixed-site level: `FiniteSheafHomCocone` consumes
the literal tuple `sheafSections` cocones and returns a certificate for the
complete original composite functor. The concrete consumer then specializes
one whole certificate. For the limit-family extension, give the existing
cochain isomorphism explicit source and target complexes before applying native
`IsColimit.extendIso`; do not ask instance synthesis to normalize its inverse
through concrete family-model aliases.

Graph164 accepted the fixed-site leaf in 25 seconds and the actual scheme
cochain consumer in 14 seconds, with unchanged resource limits and options.
The certificate still assumes only the original evaluated tuple cocones, not
a colimit of the whole sheaf cocone. No benchmark, extra test, audit, or kernel
replay was run for this record.

### Original section images: explicit relative arrows and pointwise native interfaces

The final original-section image equation repeatedly reached the normal kernel
heartbeat or memory guard when equality-rebasing two relative chart objects
under the original section functor. The two objects had the same underlying
pullback scheme but differently associated structural maps. Moving primitive
section-map normalization to a shallow canonical gluing interface was useful,
but did not by itself remove this dependent carrier conversion.

Keep those relative objects separate. `RelativeChartComparison` constructs
actual identity-underlying Over arrows in both directions and proves their
source and representative triangles without coefficients. Functorial
restriction along these arrows yields the original relative separation
interface. Likewise, `RelativeChartTransition` isolates the actual pullback
lift and its triangles before introducing the coefficient sheaf.

For map-square element algebra, use an opaque arbitrary functor with intermediate
values equal to the original `etaleRepresentativeSection` terms. Those values
already have the required functor-object types. Do not replace them with explicit
étale-evaluation inverse seeds, which reintroduce the earlier carrier mismatch.
The final geometric specialization is a pointwise chart equation with exactly
the same literal original Over arrow in its statement and result. The family
image theorem then only applies separation to these pointwise equations.

Normal graph169 compilation on baseline 2c34f185 accepted
`MappedCoverSectionRepresentatives` and `StageSectionsImage` in 10 seconds each.
The preceding graph168 accepted the independent original relative separation
leaf in 59 seconds. No resource limit, mathematical hypothesis, or original map
was changed, and no extra test, benchmark, audit, or kernel replay was performed.
This validates the actual image equation, not yet the full continuity endpoint.

### Normalize original fibre-product cohomology before geometric specialization

The geometric fixed-coefficient diagram reached the normal kernel timeout while
converting its all-degree transition to the original fibre-product restriction.
A direct rewrite first failed at the hidden base-cone carrier. Moving the rewrite
to a concrete coefficient equality or a concrete cohomology `congrArg` still
expanded the geometric system, native chart morphism and coefficient evaluation.

Separate the actual scheme structure/map equations, then compare the whole
original `pullbackTriangleIso` before evaluating it at the coefficient sheaf.
A generic fixed-system component lemma must retain the literal
`pullbackCoefficientTransition` in its conclusion. Finally, normalize the
original `fibreProductCohomologyRestriction` at arbitrary native étale objects,
before supplying geometric-neighborhood objects. Its input includes both actual
scheme arrows and the heterogeneous equality of their coefficient maps. Merely
normalizing an abstract `H.map` composite and converting to the native restriction
after geometric specialization did not resolve the timeout.

Graph173 accepted `GeometricCohomologyDiagram` in 62 seconds on f27c5fa9, with
independent Ext universes, unchanged original maps and no changed resource limits
or elaborator options. This records acceptance of the actual stage map, not a
benchmark or a proof of strict-local cohomological continuity. No extra test,
audit, repeated validation or kernel replay was run.

### Form the original relative-section bifunctor before evaluating coefficients

The scalar base-change naturality proof in
[PullbackSectionsBase](../Aglib/AlgebraicGeometry/EtaleCohomology/Continuity/PullbackSectionsBase.lean)
reached the normal kernel budget in graphs 127 and 177. Giving the same scalar
equation typed helpers did not resolve the conversion: specialization still
expanded the original Over-map structural arrows, inverse-image comparisons,
and coefficient evaluation simultaneously.

Keep the coefficient variable at the functor level. The actual
`pullbackSectionsBifunctor` uses the original global-section unit and original
triangle comparison as its arrows. Prove base-change naturality as an equality
of whole natural transformations, then evaluate this bifunctor at the chosen
coefficient sheaf. The resulting evaluation is definitionally the original
relative-section functor. Its restriction to the actual small-etale site is
therefore naturally isomorphic to the original inverse-image sheaf, with no
new sheaf or continuity hypothesis. Avoid inserting an identity associator
inside the component comparison when the native functor endpoints already
agree; keep genuinely necessary outer reassociations explicit.

Graph 181 accepted the full leaf in 79 seconds on baseline f27c5fa9, under
Lean 4.34.1 and the pinned Mathlib version, with the original resource limits
and elaborator options. This is native acceptance evidence, not a controlled
benchmark or a proof of scheme-limit section continuity. The actual affine
section descent and eventual-equality producers remain separate obligations.
No extra test, audit, repeated validation or kernel replay was performed.

### Compare whole unresized cohomology diagrams before shrinking groups

The geometric stage comparison repeatedly reached the normal kernel heartbeat
or memory guard when combining original system-H object aliases, native chart-H
objects and `Shrink` in one concrete value or morphism equation. Generic additive
cancellation and a whole small-presheaf map lemma did not remove the conversion
at their geometric specialization; graphs177,179,181 exposed that boundary.

Construct the original unresized fibre-product H functor first, reusing its
already proved actual restriction identity/composition laws. Compare the whole
geometric system-H diagram with that original diagram in its independent Ext
universe, before introducing any `Shrink`. Keep the independent original
neighborhood-colimit/stalk germ supplier separate from resizing naturality.

Graph183 accepted `FibreProductOriginalDiagram` in 76 seconds,
`GeometricOriginalDiagram` in 29 seconds and the independent
`GeometricCohomologyStalk` in 24 seconds on f27c5fa9. This validates the original
whole-diagram comparison and native germ supplier, not yet their resized
whole-diagram consumer or strict-local cohomological continuity. No resource
limits or elaborator options changed, and no benchmark or extra validation was run.

### Keep original chart unit and coefficient-square maps whole until evaluation

The original etale chart-square section comparison reached the normal kernel
budget when a whole square identity was specialized to a coefficient and then
combined with the original unit-representative equation. Generic scalar factor
lemmas and typed composition aliases did not remove the dependent carrier
conversion: graphs 180, 182 and 185 still expanded the original Over arrow,
chart evaluation and inverse-image composition together.

Retain both actual transformations before evaluation.
`DiagramEtaleSections.squareSectionsNatTrans` is the original section pullback
followed by the original coefficient-square inverse. `unitSectionNatTrans`
is the original adjunction unit followed by restriction on the specified test.
Use the native relative-section bifunctor for the original Over arrow, package
the existing representative equation in the coefficient functor category, and
cancel the original composition isomorphism there. Evaluate the resulting whole
equality only once. Separate generic component normalization from concrete
chart specialization; the final theorem still names the literal
`squareSectionsMap`, original adjoint coefficient component and restriction map.

Graph 187 accepted the full leaf in 24 seconds on f27c5fa9, with unchanged
resource limits and elaborator options. Graph 182 separately accepted the
actual test-diagram geometry in 4.3 seconds. These are canonical map identities,
not section-colimit certificates or higher continuity. No extra test, benchmark,
audit, repeated validation or kernel replay was performed for this record.

### Rebase sections to the terminal coefficient chart before equality descent

The affine section eventual-equality proof initially refined two finite
representative covers, restricted both sections to actual base-change charts,
and descended all representative equalities simultaneously. The mathematical
route was valid, and its geometric and generic equality suppliers compiled,
but concrete scalar specialization repeatedly exceeded the normal kernel
budget. Splitting wrappers, aligning Over arrows, introducing correctly typed
native seeds, and evaluating whole coefficient squares did not close that
concrete boundary. Those unsuccessful drafts are not acceptance evidence.

Once the original fixed-base section natural isomorphism was available, the
finite-cover route was unnecessary. For a stage map `r`, set the coefficient
sheaf on that stage to the original `r⁻¹F`. Its global sections are coefficient
values on the terminal étale chart. Use the original base-change natural
isomorphism, with an explicit identity-underlying Over arrow at the initial
stage, to turn equality of original limit images into equality of two terminal
representatives. Apply the existing actual affine representative-equality
descent theorem, then reflect equality through the same natural isomorphism.
This avoids all concrete pullback-chart scalar criteria while retaining the
literal original section maps and without adding a continuity premise.

Keep the terminal `τ ≫ 𝟙` source normalization explicit: transport equality
along the original Scheme-arrow equality before instantiating the dependent
representative carrier, rather than asking `simp` to rewrite that carrier.
For the identity representative use the explicit original functor `map_id`
equation followed by `ConcreteCategory.congr_hom`, rather than rewriting
inside an already exposed concrete coercion.

Graph 191 accepted the complete `StageSectionsInjectivity` leaf in 5.6 seconds
on f27c5fa9 after graph 189 had only ordinary native-alias errors. Its actual
public endpoint is `exists_stage_sections_eventually_equal`, for the original
same-stage section maps. The source retains the affine-stage and small-index
hypotheses; it does not claim full scheme-limit continuity. Resource limits,
options and dependency pins were unchanged. No benchmark, extra test, audit
or kernel replay was run for this record.

## Bounded presentations: preserve typed section transport

Affected declaration:
`AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.BoundedPresentation.generators_isSeparating`
in `Constructible/TorsionColimit/BoundedPresentation.lean`.

Private basis 2c34f185fa859e862661f939cd216b07bcccfb26; Lean 4.34.1;
Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.

The first module version, SHA256
32ae530eddea5ee1ebadae05f910fe0925be79ff51b35986fbb9d9835ea36f39,
exhausted the standard 200000 elaborator heartbeats at `whnf` in
remote-4f8d706226d14488959cf43eb95b836d, source snapshot
1c8814701ec3705c9023b2f01a9f106b309d7c0f8c90f062e6727655851dedd2.
The generated downstream unknown
`generators_isSeparating` diagnostic was cascading; no endpoint from that
module was admitted by the failed run.

The repair first uses the actual single-index constructor of
`ObjectProperty.ofObj`, rather than trying to treat it as an existential
pair. The subsequent section calculation keeps the original free mod-n
cokernel carrier behind the named `sectionsEquiv` boundary. A typed
`sectionsEquiv_symm_naturality` equation transports the actual coefficient
arrow on an unchanged section. The proof composes these exact equations
instead of simplifying the concrete affine restriction and free-cokernel
carrier. Native reflection-of-isomorphism instances are installed at their
fully typed original maps. The final filtered presentation also uses the
actual costructured-arrow category and its explicit standard-universe
`SmallModel`, with essential smallness proved from the finite-colimit closure.

The unchanged mathematical construction uses actual sheaves killed by n,
original free ZMod representables on affine etale tests, the original
coefficient maps, and the original underlying colimit cocone. No constructible
presentation or finite cogenerator premise was added; stages are still only
proved to belong to the genuine finite-colimit closure. No heartbeat or
resource ceiling was raised.

Actual successful scope: exact BoundedPresentation module SHA256
 d07e613bffcdd8d1d38887ad81e02435466e9643ed0a1acd420f6bb51cba66ec,
accepted as one frontend in remote-0ee44936a46b4f95b2601122b7c5763e,
source snapshot 6fb90108db4177e899d229330ed65e1e9106c7d31be7f96167cd86df3e98db3c,
reported 6.2 seconds, standard 200000, no diagnostics in that leaf. The same
invocation accepted Sections and failed the separate Bounded leaf; this
records only BoundedPresentation coverage. These are ordinary existing
proof-iteration observations, not a controlled benchmark or a diagnosis of
a Lean defect. No additional profiling, replay, audit, or benchmark was run.


## Convert the coefficient family before specializing the canonical exchange

Basis: private Aglib HEAD `2c34f185fa859e862661f939cd216b07bcccfb26`,
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1.
This records existing scoped compilation observations. No benchmark, replay
or additional check was run, and the ordinary budgets were unchanged.

Run `remote-1863ac2989664358a4a7f2d9e15a72bb`, source snapshot
`f05d77f18121237fffa1bace745947db2dd16e8efce3c8ffa64f12266795a271`,
compiled `AllModuleCoefficients` successfully in 9.3 seconds, then rejected
the two concrete bounded-coefficient composition/descent declarations with
**kernel deterministic timeout** diagnostics. `BoundedCoefficients` source
`83b15994453093d37b94c1f82c29b97b4277dce8562d323f5bb0eadc0b92d981`
took 295 seconds according to its actual frontend log. The unknown-constant
errors in its two higher wrappers were cascading consequences.

The failing wrappers converted the hypotheses inline:

```lean
fun J _ => hOuter _ (zmodUnderlying_nsmul_id X n J)
```

This supplied the literal `beta.app (single (underlying J))` test where the
compiled injective reduction used the protected regular `zmodSingle` head.
The effective repair moves that conversion to a typed generic boundary
**before** specializing the original exchange. The bridge takes

```text
single : A -> B, U : M -> A, Z : M -> B,
e : Z = U followed by single,
beta : L -> R, P : A -> Prop,
h : every P-coefficient has invertible beta on its single,
hU : every injective I satisfies P (U I).
```

It substitutes the whole functor equality with variable `beta`, then returns
the injective tests directly at `Z.obj I`. The concrete consumer supplies
the already compiled original `zmodSingle`, its whole original functor
equality by `rfl`, the actual underlying functor, and its actual annihilation
theorem. Both concrete wrappers then pass tests with exactly the same shared
data head as the compiled injective provider.

The public bounded-coefficient signatures are unchanged: they use the
literal original single of the actual abelian coefficient. The canonical
`derivedBaseChangeMap`, every higher-image map, all six independent abelian
derived-category universes, and the actual modulus hypothesis are unchanged.
There is no new mathematical premise, alternate coefficient or exchange.
The bridge preserves the actual original object and arrow formulas through
the existing `zmodSingle_obj` and `zmodSingle_map` identities.

Validated source:
`4d8eb96a1d6e9595c34236da6d95d7aff0fb27ab23c08729715b906ea2393385`.
Run `remote-92dc3e6bec274704977cd8711ecec024`, source snapshot
`044e3e0d4434e59e6509c9ca93d56224055c88aaee1f393e64efe8afdcf4d3ab`,
compiled the complete bounded leaf in 5.5 seconds and its original
all-degree `HigherReduction` consumer in 4.9 seconds. This final run had
exactly two actual frontends, both successful, with exit code zero and
14.42 seconds overall wall time. Earlier matching leaf successes were
reused; the Lake progress index is not a count of fresh frontends.

The comparison records the successful proof boundary, not a performance
ratio or a diagnosis of a Lean defect. Existing logs, receipts and compiler
events remain under the two run IDs in this task's `remote-runs/` directory.


## Share the actual coefficient-single data head before transporting exchange tests

Basis: private Aglib HEAD `2c34f185fa859e862661f939cd216b07bcccfb26`,
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1.
These are ordinary scoped compilation observations, not benchmark runs or a
compiler-defect diagnosis. The standard 200000 declaration-heartbeat limit
was retained throughout.

The original `InjectiveExchange` assembled canonical vertical-pasting,
acyclic-single comparisons and actual coefficient retracts directly at the
expanded original `singleFunctor.obj (zmodUnderlying.obj I)` terms. Run
`remote-b72d18ebd6954922a783d46bbfa25a12` failed both concrete reduction
theorems with **kernel deterministic timeout** diagnostics. Its leaf source
was `a78dbd5ed97cfc826a9acd1209c29fc475dcab92bef7261cb1b3006742ab846d`;
the log reports 280 seconds for that frontend. The later unknown-constant
diagnostic was a consequence of the rejected descent declaration.

Extracting only the logical transport into generic `NatTrans` injective-test
lemmas was insufficient. In `remote-ceb0c3469fbd493a9444108bdba76e26`, package
`d874a1584ea2cb92369a63b6786e192c0667cd3c8a62f8730ee1e800c3fe1cfb`,
leaf source `dc58e249c88670ef11a799230886b18d907c1cadb7fa455e2f8a373664277142`
again failed both concrete wrappers with kernel deterministic timeouts. The
log reports 247 seconds for this frontend. No accepted theorem or broader
scope is inferred from either failed invocation.

The effective repair gives the actual coefficient embedding one shared
regular data head:

```lean
def zmodSingle (X : Scheme.{u})
    [HasDerivedCategory.{dX} (AbelianSheaf.{u,u+1} X)] (n : ℕ) :
    ZModSheaf X n ⥤ DerivedCategory.Plus (AbelianSheaf.{u,u+1} X) :=
  zmodUnderlying X n ⋙
    DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u,u+1} X) 0
```

The exposed `zmodSingle_obj` and `zmodSingle_map` formulas are `rfl` and
retain exactly the original object and coefficient arrow. A separately
typed `zmodInjectiveImageSingleIso` returns the previously compiled native
`derivedDirectImageZModInjectiveSingleIso` at these same shared heads. It is
the original acyclic-single comparison from the original right-derived unit.
The generic injective-test composition/descent proofs and the concrete
theorem statements use this identical functor head. The canonical
`derivedBaseChangeMap`, native vertical-pasting and genuine coefficient
retract suppliers are unchanged. No new mathematical premise, alternate
exchange, or injectivity-after-forgetting claim is introduced.

The source interface is normalized to use the shared actual functor; an
unused draft higher-injective wrapper was omitted. The direct original
all-degree reduction consumers remain in the separate upper leaves. No
additional fully expanded certificate was pursued merely to reproduce the
failed conversion.

Validated leaf source:
`e0bf719ae8240bbb4c652648cc7d84cdcd91b2d2c0a05e6de3aab2c5751f24fe`.
Run `remote-5343d4769a9c40948d7108ee21f8548d`, source snapshot
`b8e6140d19600b44c67df20b2b06ce171dc61349e620227ac4396e464a52d849`,
compiled the complete `InjectiveExchange` leaf successfully in 5.4 seconds.
Its two-frontend batch **failed overall**, because the independent
`ExchangeShift` leaf had four ordinary elaboration errors. That run is not
a successful whole-family or proper-base-change closure claim.

The pre-execution snapshot-guard stop reported as invocation `70101` did
not execute a compiler and is not additional proof-failure evidence.

All cited logs and receipts are the existing artifacts under this task's
`remote-runs/` directory. No benchmark, replay, lint or additional build was
run to prepare this note.


## Use the native isomorphism-to-monomorphism constructor directly

Basis: private Aglib HEAD `2c34f185fa859e862661f939cd216b07bcccfb26`,
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1.

The generic `Plus.InjectiveComparison.homology_mono_successor` uses an actual
injective presentation and its actual cokernel. In the failed run
`remote-ceb0c3469fbd493a9444108bdba76e26`, package
`d874a1584ea2cb92369a63b6786e192c0667cd3c8a62f8730ee1e800c3fe1cfb`,
source `5f07c5e041f5c4a19a393b1a23c4531155bd081f653bab01ee1837eeec376a26`,
the already available preceding-degree isomorphism hypothesis was installed
locally. A subsequent `infer_instance` for monicity of precisely that
homology-comparison arrow exhausted the native 20000 typeclass heartbeats.
The diagnostic was at line 131, on the actual cokernel of the chosen
injective presentation. This was not a kernel timeout or an OOM.

The effective repair changes only that final instance search:

```lean
have := hPrev (cokernel P.f)
exact IsIso.mono_of_iso _
```

The existing native constructor consumes the same local isomorphism proof
and yields monicity of the same original arrow. No extra mathematical
premise, altered cokernel, comparison map or search-budget override is used.
This records the validated proof boundary, not a diagnosis of why the wider
instance search visited its particular alternatives.

Successful source:
`7e54af9098fc49f2b09564e30facada627d7ab8b4a05c89d0c460e8c1cd7fc6f`.
Actual run `remote-513fd164d7b74707b30c0616780ee6cb`, package
`fdd10aa46960815795782d7e809e939a2bd275f674631b5faf2818e97276c14e`,
compiled this leaf in 12 seconds. The three-frontend scoped batch passed all
three selected leaves; its other two were `GeometryCriterion` and
`SingleHigher`. The enclosing run succeeded. No replay, benchmark, lint or
extra check was run to prepare this note; the ordinary 200000-heartbeat
declaration limit and 20000 typeclass limit were retained.

Evidence is in the two runs' existing `build.log`, `receipt.json` and
`compiler-events.jsonl` under this task's `remote-runs/` directory.


## Pinning the actual module universe in a Kan-extension preservation proof

Basis: Lean 4.34.1, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`,
Aglib private HEAD `2c34f185fa859e862661f939cd216b07bcccfb26`.
This records ordinary author repair, not a benchmark or a compiler-defect claim.

The failed run `remote-a6f5a8f9129a467b96fc8a03d1aadb5c`, source snapshot
`35ac35bf7c7b5e64ad72036331dc00b219fe0d0cf0a9fe9dc970228ae06dd8a5`,
reported a stuck universe constraint at `ZModImages.lean:93:2`:
`u + 1 =?= max (u + 1) ?u`, while synthesizing limits of the actual
`ModuleCat.{u + 1} (ZMod n)`. Earlier explicitly typed functors and comparison
isomorphisms alone had not fixed the unresolved universe of the limit instance.
The mathematical statement and ordinary 200000-heartbeat limit were unchanged.

The successful proof keeps the native comparison
`V.lanCompIsoOfPreserves G.op`, with `V` the actual module-to-abelian forgetful
functor and `G` the actual small-etale site base-change functor. For each finite
shape `J : Type (u + 1)`, it installs the exact native instances

```lean
ModuleCat.hasLimitsOfShape.{u + 1, u + 1, u + 1, 0}
ModuleCat.forget₂AddCommGroup_preservesLimitsOfSize.{u + 1, u + 1, u + 1, 0}
```

and then explicitly constructs preservation for both postcomposition functors
with `whiskeringRight_preservesLimitsOfShape`, fixing the actual source,
target and shape. Reflection of those limits and the original Kan comparison
prove preservation for the module Kan extension. No extra mathematical
premise or alternate inverse image was introduced.

Validated leaf SHA-256:
`a5e16619ecc3507b42737d94be44a13d8ae1418d5de3a42f5a0e0ae0734d27ba`.
The run `remote-0af3ec46961642fe80cacaa0f3f9a10a`, source snapshot
`bbe7c640f9c3b77652f248f6782d497315ba3d870818777bc7b2113af0a95d98`,
compiled this actual leaf successfully in 5.8 seconds. Its same four-frontend
batch also compiled `HigherImageAcyclic` and failed only the two other
dependent leaves `ZModRetract` and `ZModAcyclic`; the overall run status is
**failed**, not a successful closure claim. No additional benchmark, replay
or verification cycle was run for this note.

Exact local evidence:

- `remote-runs/remote-a6f5a8f9129a467b96fc8a03d1aadb5c/build.log`
- `remote-runs/remote-0af3ec46961642fe80cacaa0f3f9a10a/build.log`
- Both runs' accompanying `receipt.json` and `compiler-events.jsonl`.


## Keep native shift structures explicit in the canonical exchange proof

Basis: private Aglib HEAD `2c34f185fa859e862661f939cd216b07bcccfb26`,
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1.
The ordinary 200000-heartbeat declaration budget and native instance-search
budget were retained. These are existing scoped compilation observations,
not benchmarks or an additional verification cycle.

The failed `ExchangeShift` source
`6e394111247e039aa7b488409081d13fff411dfa39b55a5612a04c27e2ec00ea`
was compiled in `remote-ceb0c3469fbd493a9444108bdba76e26`, package
`d874a1584ea2cb92369a63b6786e192c0667cd3c8a62f8730ee1e800c3fe1cfb`.
After building the original derived inverse-image comparisons, direct
instance search for `NatTrans.CommShift` on their concrete two-factor and
three-factor isomorphism chains exhausted 200000 heartbeats at `whnf` or
`isDefEq`. The same leaf also exposed a separate actual coherence mismatch
in its identity-on-complexes comparison and a missing import of the existing
bounded-below quasi-isomorphism shift instance.

The effective repair has three parts.

1. The original degreewise identity comparison is postcomposed with the
   fully faithful native complex inclusion. Its displayed chain includes
   both the right unitor and the final inverse left unitor. The latter
   retains the target functor as `Id ⋙ inclusion`, with its actual composite
   `CommShift` structure, rather than identifying only the underlying
   functor with `inclusion`. The original chain components remain identities.
2. The existing `CochainComplexPlus.QuasiIsoShift` provider is imported;
   no new shift-stability premise is assumed.
3. Private typed `isoTrans_commShift` and `isoChain_commShift` prove the
   native composition law over variable functors and their supplied native
   shift structures. The concrete inverse-image comparison and original
   square supply those same factors to these regular proof heads. This
   avoids asking instance search to reconstruct the expanded geometric
   comparison chain. It does not choose another shift structure or another
   inverse-image square.

The original derived-adjunction unit is shown shift-compatible through its
original unit factorization. Its two right-derived units and original
degreewise adjunction unit are retained. Only the exact left functor's unit
is inverted; the nonexact right-derived unit is not cancelled. The original
adjunction mate consequently has the original canonical shift compatibility.
There is no additional public scheme hypothesis.

After the performance repair, `remote-5343d4769a9c40948d7108ee21f8548d`
reported only four ordinary elaboration errors, with no remaining timeout.
These were repaired by using `NatTrans.ext` followed by `funext K` instead
of allowing `ext K` to descend to the full-subcategory morphism's underlying
`.hom`, and by naming the two original `derivedImageAdjunction` compatibility
facts at their exact types. `remote-3daf87dbe5e24b0dab8cb23955db4394` then
reported only a local-let normalization and an associativity equality;
explicitly unfolding that local `Q` and applying `Category.assoc` closed them.
Neither intermediate failed invocation is claimed as a successful provider.

Complete validated leaf source:
`19875b7f834ee4099fcc6d1a3d87e7d96f7dc3fff57a9900a4e2171060072534`.
Run `remote-aa4f8a36498e4ef3a3da29f4fab9b1cb`, source snapshot
`00847f07b44899f9f17b527183df7bcfa0ce7a173f0703df630ea87c6c01de2a`,
compiled `ExchangeShift` successfully in 6.1 seconds. That two-frontend batch
**failed overall** at the separate upper `AllModuleCoefficients` parser
error, so the evidence covers the complete shift provider only. It is not
whole-family or proper-base-change closure evidence.

The actual logs and receipts are preserved in this task's `remote-runs/`
directory. This note diagnoses the successful typed coherence boundary,
not a Lean compiler defect or an asserted performance ratio.

## Keep the original universal exchange test at a shared data head

Basis: Lean 4.34.1, Mathlib `d13f23b`, and the published proper-reduction
suppliers retained at `f464f6b`. The first
[universal-property](../Aglib/AlgebraicGeometry/EtaleCohomology/Proper/Universal/Basic.lean)
source, SHA256
`e55d71f9f83faeca6b0e1ce20a0eeede7e3f61bf303a02c43c5e1da0e975428a`,
failed in `remote-6260a813bb0f4c8e91ea0dcd44ab8a90`. Its actual
surjective-descent declaration exhausted the kernel's deterministic budget;
other diagnostics concerned concrete pullback transport and implicit object
quantifiers. No budget was raised.

The repair defines one regular `boundedExchange` predicate for the original
all-degree, all-n-killed-coefficient test. Generic composition and descent
helpers consume and return that same head before actual Cartesian squares
are supplied. In composition, the actual pullback triangle is retained by
`clear_value a` and substitution of its original equation before applying
the generic helper. Explicit theorem applications preserve the entire
implicit object quantifier in universal finite membership and descent.
The original exchange maps, coefficients and hypotheses are unchanged.

Final source
`7a56a974fbf33818e1b21f54654a9c68c705cbb2ce939a92254af797569cbf1f`
passed the complete leaf in `remote-0b94a03fbf9447e1a503ae0b5cf1097e`,
with one successful frontend and 9.64 seconds for the remote build action.
This reuses ordinary compiler evidence; it establishes removal of the
observed timeout, not a controlled speedup or a compiler-defect diagnosis.
The separately compiled model transport retains four independent model
universes; final projective-line exchange is still a mathematical input.

## Use a finite original-unit calculation for constant direct-image coordinates

In the finite-constant
[represented-coordinate supplier](../Aglib/AlgebraicGeometry/EtaleCohomology/Constructible/FiniteCogenerators/AffineIntegralConstants/RepresentedSections.lean),
run `remote-442a6e3ab1a34db3a105414977b08fb5` diagnosed a potentially looping
simp rule and exceeded maximum recursion depth. The original calculation
combined forward `Functor.map_comp` and associativity with reverse
`Functor.map_comp_assoc`. This was a rewrite loop; it was not a measured
heartbeat timeout.

The repair is a finite calculation using forward functor composition, the
original adjunction-unit naturality equation, and explicitly typed
identity-map equations transported by `congrArg`. Projection lemmas retain
the exact original `Scheme.Etale.forget` object heads. The final residual
projection mismatch in `remote-6039f2c31878477ca53093e34b01bd76` was repaired
at that same head. No recursion or heartbeat budget was raised, and the
original maps and mathematical assumptions were preserved.

Exact source
`458ea48f66e37deba72898fd309dde62d9bbc5a57d77834b9a720c7c2a6800da`
passed `remote-df229d88e13c44a58e0467cc3745c13e`: one successful frontend,
no diagnostics and 15.27 seconds for the build action. Lean and Mathlib
remain at the pinned versions above. These existing observations do not
supply a benchmark, profiling attribution or broader mathematical closure.

## Assemble normal generic triangles before the concrete integral closure

On Lean 4.34.1 and Mathlib `d13f23b`, the first
[normal generic model](../Aglib/AlgebraicGeometry/EtaleCohomology/Constructible/FiniteCogenerators/NormalGenericModel.lean)
source `90df91ee9a26693d0a1cbaac567e7a03483bbfb032132d5cb1100003c657a8b2`
failed in `remote-49522076a3ac4507bffb6d65c2b974bc`. It had scalar-tower
orientation and native function-field instance errors, plus a 200000-heartbeat
whnf timeout at concrete integral-closure specialization. The next failed
run `remote-b9f30b7bfd174e72a1255b5d20eb63a3` retained instance failures and a
constructor timeout; neither run supplies accepted source.

The passing implementation supplies the named native
`StructureSheaf.stalkAlgebra` and `functionField_isFractionRing_of_affine`
producers. It proves the original localization triangle at abstract R,C,L,
then assembles its complete original field-map equation and constant
trivialization at abstract R,C,K,L. Only that complete constructor receives
the actual integral closure. Typed scalar-tower equations retain the literal
structures. The canonical field point is `IsLocalRing.closedPoint Q`; default
point instance search had failed separately. The actual maps and assumptions
are preserved, and the integral closure remains possibly infinite.

Exact source
`2a46fc5b9ddbce8bd67452bf5a75993407da9dc2ef99a2f313d347560004da5d`
passed its complete frontend in `remote-8950dd65f65242898c09150d9b16957d`,
reported as 32 seconds, at unchanged standard budgets. The outer graph failed
on the separate Spectrum consumer. This validates the repaired leaf without
a benchmark, unique compiler-cause attribution or claim of a finite
normalization.

## Retain complete product families through finite-stage factorization

The original
[Spectrum](../Aglib/AlgebraicGeometry/EtaleCohomology/Constructible/FiniteCogenerators/Spectrum.lean)
assembly encountered a dependent rewrite motive, a categorical `Pi.map` name
collision and product projections retaining different constant-cocone heads.
Source `64f138c7d25789632b4ccd8aebfd8fe5a4d85dc6392565c8ffcf48c8137b1465`
also timed out at 200000 heartbeats in `remote-02dc218e3235421c94394cbf8a1605e1`,
while an ordinary projection type error remained. The later ae862b49 source
reported only a calc Trans inference error, without a timeout. These mixed
repairs do not identify one cause of the earlier cost.

The final proof names the actual `normalModelTargets` family and its original
`normalModelProduct_π` equation. Typed associativity, `congrArg` and `Eq.trans`
transport those complete equations; `CategoryTheory.Limits.Pi.map` is qualified.
The product-monicity factorization is proved at abstract categorical objects
and supplied with the entire actual cocone and model packet. This preserves
all finite values, actual stage arrows and the original mono.

Source `b19fec9aba152326f896fda0e5665155f127a6110f796388bc90f10dbb7d0506`
passed its complete frontend in `remote-9c333911ae764c3fa4aa3ffb6ae96062`.
Its Affine consumer initially failed on another projection normalization.
The same typed equation boundary repaired exact Affine source
`7cca91d19ee404a79ec80ce7c928e89a5b046d4c8c7bba30742996bd69f03c3c`,
which passed `remote-1848273a3a744f19ba71b722e32c481c`: one fresh frontend,
no diagnostics, 5.864 seconds between compiler events. Ordinary budgets were
unchanged; these existing observations are not a controlled speedup, profiling
experiment or broader verification cycle.

## Pass the preservation dictionary of an equivalence explicitly

In [GenuineModules](../Aglib/AlgebraicGeometry/EtaleCohomology/Constructible/PositivePresentation/GenuineModules.lean),
`genuinePresentationCoconeIsColimit` transports an original cocone through
canonical scalar conversion, an actual equivalence. In
`remote-2f45842a61de4ea99587e88fe0e0f568`, implicit synthesis of
`PreservesColimit D (scalarLift X n)` reached the standard 20000
instance-search heartbeat limit at that declaration.

The repaired proof obtains `PreservesColimitsOfShape I (scalarLift X n)`
explicitly from the equivalence's adjunction, projects its
`preservesColimit` dictionary, and applies the dictionary's `preserves`
field to the original colimit. Extension by the original `canonicalModuleIso`
retains the point and literal underlying cocone equations. No global instance
or heartbeat change is required.

Exact source `92e86ad7a778777b15dff05050c4c6ef72b83d89690aef793c0c8d321986a2b5`
passed in `remote-3d9b7fc4a13f4c429e8fbc0df4b09070` (6.1 seconds reported).
That graph also contained a failing separate AffineRestriction child; only
this passing leaf is credited. These retained observations validate the
repair, not a controlled speedup or a profiling experiment.

## Name local instances in independently imported public modules

`local instance` controls instance search scope; it does not make its generated
constant name private inside a public section. Independent branches in
`Stalk/GeometricCohomologyDiagram.lean` and
`Stalk/GeometricLimitCohomologyCocone.lean` generated the same public HasExt
instance name. Each module compiled separately, but the shared native lint
and audit import failed in `remote-fe2c1151635345c6bc8467a75a2a441d`.

The repair gives the latter module's three local instances explicit,
module-specific names. Their types and bodies and the public theorem proofs
are unchanged. Exact source
`24f8f134a44294e235caadcbff5ddfe33e051fc37e97dd4ba05b3e857fb3ba99`
passed its sole changed frontend in
`remote-865a132c04aa463f8fe3faf4c559a3af`. The next shared import succeeded
and its audit covered 36,580 declarations; that run separately reported native
naming, documentation and simp-normal-form findings. Their five-source repair
and actual affected consumers then passed 23 frontends in
`remote-4a990481bbe1449cb6734161aca0c57a`. This uses retained compiler evidence
and the ordinary shared check, without replay or a separate diagnostic chain.

## Hilbert-scheme direct images: compare isomorphism values at the `Iso` level

On 2026-10-24 `HilbertScheme/DirectImageSheafQuotient.lean` took 188 s
(remote-5a89d2ea0cc24fbc8f2dd4abc43927c9). Kernel type checking of two instance lemmas dominated
(profile remote-34601a9d7fc74950b0c7fb714406c522, threshold 500 ms):
`pullbackFreeMap_familyQuotientMonomialMap_pointMap` took 123 s and
`pullbackFreeMap_familyQuotientMonomialMap_baseChangeMap` 47.7 s. The general lemma they
instantiate, at a variable morphism `p`, took 1.7 s. Their statements use the regular definitions
`familyQuotientTwistPointIso` and `familyQuotientTwistBaseChangeIso`, and their proofs reached the
unfolded isomorphisms, by `rw` or by direct application.

Two remedies did not help: proving the instances by plain application of variable-argument lemmas
(92 s and 36 s), and unifying the two presentations of the tensor product,
`moduleTensorLeftFunctor` against the monoidal `⊗` (126 s and 46 s). Probes at threshold 100 ms
(remote-c8b57012a9c94a228657ca6a3daca159) isolated the conversion: the equation
`familyQuotientTwistBaseChangeIso … = <value> := rfl` checked in under 0.1 s, and so did the
instance stated with the value; the instance stated with the definition took 45 s.

The repair adds named `rfl` value lemmas at variable arguments (`familyQuotientTwistBaseChangeIso_eq`,
`familyQuotientTwistPointIso_eq`, `familyQuotientMonomialMap_eq`) and proves each instance as
`(congrArg (fun i => _ ≫ i.hom) _eq).trans lemma`. The module then built in 24 s under the
profiler, with cumulative kernel time 7.5 s (remote-3bb84110e86249bc9fdb4c5acdf7610d), and in 18 s
without it (remote-29575aba19604befa46fa4e8c33bd36f). Default budgets were kept; no statement
changed.

Candidate mechanism, not checked against a kernel trace: comparing `(d …).hom` with the `.hom` of
`d`'s value reduces the projection, which forces weak-head normalization of the isomorphism
structures before `d` is unfolded; at the `Iso` level, lazy delta unfolds `d` first.

When an equation's statement uses a definition of an isomorphism or morphism and its proof produces
the value, bridge them with a named `rfl` lemma through `congrArg` and `trans`, not by `rw`, `exact`
or a type-changing application. This is the method of "Hilbert-scheme naturality: rfl value lemmas
and regular components" applied to isomorphism values.

## Picard tangent space: prove additive-group algebra abstractly, then specialize

At Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, a profiled remote build
of a pre-repair `Picard/Tangent/Thickening` (run `remote-ae44f9f482d946e99dbd5c68365a0ca5`,
source `1cc92cc3`, not retained; the receipt records a whole-cgroup average of 12.0 CPU cores,
and the author's observation of a host load of about 80 on 32 cores has no retained probe)
reported, among entries of at least 10 s, kernel type checking of 36.7 s at 188:4, 13.8 s at
199:8, 25.4 s at 206:4, 80.4 s plus 21.4 s of congruence-lemma generation at 261:0, seven
entries of 18.1–69.8 s at 276:4, 42.3 s and 24.4 s at 290:4 and 296:4, and linting of 339 s at
310:0. In that source the `AddEquiv` constructions `picardRetractionEquiv` and
`UnitsCohomologyComparison.kerEquiv` proved their fields with `abel` and `rw` directly over
`PicardGroup`; the positions cannot be checked against a retained file, so the mapping from
positions to declarations is the author's reading. An earlier pre-repair version (source
`4c1c686a`, not retained) took 487 s in run `remote-38bfcbc79b2f4fad8e40f15b57e17e46` (exit 1
on the `unnecessarySeqFocus` style linter at 141:7).

Candidate mechanism, not established: the kernel unfolds the `PicardGroup` additive structure
(tensor product, dual and the quotient by isomorphism) while checking `abel` and
structure-field proofs stated over `PicardGroup`. The profile attributes the time to kernel
checking of whole declarations, not to `abel`.

Repair: the additive-group algebra (`AddMonoidHom.retractionAddEquiv`,
`AddMonoidHom.kerAddEquivOfComm`, now in `Aglib/Algebra/Group/Subgroup/KerEquiv`) is proved
over abstract `[AddCommGroup A]`, and the Picard declarations specialize it once; the `rfl`
lemma `picardEquiv_apply_fst` was dropped. The repaired module built in 273 s
(`remote-6237c559e89345668abc9c12402a5620`), then in 247 s
(`remote-c8bf07378f894e029e5dc0ef76ac076f`) and finally 243 s
(`remote-7523f430ca654fb7a18559a29077b505`) (whole-cgroup averages 8.6, 10.4 and 11.1 CPU
cores in the receipts); after the review repairs, which moved the generic lemmas out, it built
in 244 s (`remote-9f484e84e2d34695ac803d74f5040b21`) (6.3 cores). These builds are not matched
measurements, and the repair's effect on single declarations was not measured.

Rule: prove additive-group algebra over an abstract `[AddCommGroup A]`, then specialize it once
to concrete heavy groups such as `PicardGroup`.
