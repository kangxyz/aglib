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
