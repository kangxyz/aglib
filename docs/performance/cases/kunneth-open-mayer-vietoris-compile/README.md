# Original mixed-open Künneth Mayer–Vietoris compilation

The exact v19 candidate completed the requested ordinary native graph: all family modules,
the original facade, actual `StructureSheaf.Kunneth`, and the existing Mayer in-package
test. Run `remote-f95cd274ee324d4685cbb2fa1f94e2ae`, source
`cb6b9d714387e950fc43dbf2639fbf40bdf1456be4972958b2ee7a6dce2ed093`, closed with exit0.
Earlier successful providers were reused, not rebuilt for this milestone.

The final admission candidate omits two genuinely unused experimental generic modules
and replaces their import chain in two native leaves with the precise
`Mathlib.Algebra.FiveLemma` import. The theorem statements, proof bodies, Compatibility
imports and original elaboration settings are byte-identical across those two edits.
`FINAL-READY.json` binds the final15 files and the exact pre/post import hashes. V19 CPP
is evidence on its actual pre-cleanup imports; The final two changed import edges require the coalesced actual-main incremental
check; that check was pending at this handoff. This case does not claim established status,
programme/C3/C4 closure, or completion of the principal's publication gates.

## Mathematical and source boundary

The original mathematical source is `4707aaadf9432b2050204046021f2f6214e03366e9ba64fe1458d10e069a901c`;
the original744-line module is `bd06444b85d5aea9ee84ec4acb54bdc385a9bd078234e7adfd3cb15e594ad3c8`.
The pins were Lean4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Original contributor credits are preserved in the source images; incoming provider code
and evidence retained their authorship/source identity across the explicit continuation handoff.
The isolated source was HEAD `7545acd876b4ebf73f067d532ffa75263c01e26c` plus185 specified
afterimages. Those185 remained unchanged. Root later applied only the already accepted
actual-main2f `KunnethOpenAffine`9662 afterimage, outside the author's write scope;
`MAIN-CONSUMER-AFFINE-APPLIED.json` records its oldb2f guard and prior coverage.
Old6fb runs remain bound to oldb2f. There was no blanket main overlay or author Git mutation.

The first factor is the original ordinary `structureCohomology`, with the existing
`Scheme.structureCohomologyModule` action. The second factor is the original native
open cohomology on the unchanged ambient scheme. The actual product, inverse-image
opens, restrictions, difference, unsigned native Delta, finite antidiagonal, selected
biproduct/tensor distributions and `equivShrink` choices remain. The two degree-p Koszul
factors are both retained and cancel in every characteristic. The complete shifted
target families, including degree zero and the original zero-injectivity condition,
remain. Generic scalar and carrier universes remain independent.

`FINAL-PUBLIC-CORRESPONDENCE.json` checks all eight original public signature texts
against the final candidate. Seven full public declaration texts remain identical;
only the fourth public restriction-law proof body changes. Private row/square/gluing
arguments are reorganized. No public assumption, alternative cohomology model,
global instance, axiom, `sorry`, heartbeat/memory/clock allowance or disabled check
was introduced. Root owns affected independent mathematical review and final adoption.

## Measured scope

The original successful monolith frontend took2438.094314s (40.63min), run
`remote-e0c8307e34384514adc46fce9eb2c00f`; its parent build was later cancelled130.
That module pass is retained. No old per-frontend CPU/RSS or phase profile exists,
and no unchanged40-minute replay was performed.

Accepted unprofiled frontend observations for the fifteen required family modules:

| Module | Frontend seconds |
| --- | ---: |
| `LinearAlgebra` | 6.157831 |
| `Rows` | 191.381645 |
| `RestrictionBasic` | 100.097846 |
| `Boundary` | 280.938448 |
| `RestrictionLinearAlgebra` | 2.529537 |
| `RestrictionAssembly` | 2.829854 |
| `RestrictionValues` | 137.169008 |
| `Restriction` | 130.726776 |
| `SourceEquations` | 269.412019 |
| `FirstSquare` | 101.693065 |
| `SecondSquare` | 88.120485 |
| `Compatibility` | 2.492779 |
| `GluingInjective` | 81.066435 |
| `GluingSurjective` | 45.321609 |
| `facade` | 78.391420 |

The sum is1518.328757s (25.31min) across separate compatible incremental runs; the
longest observed frontend is280.938448s (4.68min). This sum is not parallel DAG wall
time or a controlled cold-build speedup ratio. Background load and cache conditions
were not matched to the original monolith. The actual consumer `Kunneth` passed in
35.212268s and the existing Mayer test in18.718337s on v19. Thus closure and observed
cost include actual consumers; a lower-provider pass alone is not presented as a
no-moved-cost result. `FINAL-TIMINGS.json` and the run/event ledgers retain precise
source, scope and timing boundaries.

All ordinary runs kept the admitted8-job/4-thread/12800MiB per-frontend,
65536MiB aggregate profile, default heartbeat200000 and enabled kernel/compiler/
command-linter checks. The two retired generic modules also passed (2.593129s and
2.296074s), but are not counted as required final family modules.

## Effective changes and failed approaches

1. **Retain both original module families before native specialization.** The first
   ordinary cohomology module is canonically packaged with its exact existing action;
   native open modules provide the second family. Complete variable-module tensor
   maps, exactness and distribution laws precede specialization. The complete Rows
   provider passed in191.381645s, versus retained v2 Rows918.516969s. A matched
   unprofiled first-construction prefix pair was103.896→23.732s in run
   `remote-a1fba1816e544bbba0033cad9d820064`; it supports only that bounded method.
   Earlier v3/v3a shifted-family failures were repaired by supplying the entire target
   family, not by guessing degree-zero values or raising budgets.
2. **Keep producer carriers and actual mapped arrows.** V4 Compatibility939 failed
   in761.463588s: its difference equation used public-KSum projection type arguments
   where the producer retained its bundled tensor sum; a native rewrite failed under
   implicit transparency; and a public naturality equation met a manually rebuilt
   target arrow. The repair retains producer tensor-sum carriers and proves original
   preimage-arrow identities over a variable presheaf before specialization. Source
   equations passed after a102-character line was wrapped; that prior longLine-only
   exit1 was not relabeled as CPP0. Both square modules ultimately passed.
3. **Return the literal original whole-map conclusion.** The first three public
   restriction declarations are cached in RestrictionBasic. A complete generic
   tensor-sum law passed, but its native component-proof application failed at49.
   Inferring the original component arrow allowed equation construction, yet final
   conversion still failed. A bounded file-marker diagnostic reached both equations,
   not AFTER_EXACT; AFTER_DECL was error recovery. The final assembly takes the
   original whole restriction and Künneth maps and their original generator laws,
   so its conclusion is the literal public goal. The native generator-law proof
   uses the original constructors and `apply DirectSum.lmap_lof`, matching the whole
   indexed family before an isolated element; the earlier underconstrained term
   application failed. Values and the whole native restriction law then passed.
4. **Complete the presheaf difference square before concrete composition.** The first
   square passed. The second failed at the native transitive join between an original
   middle-map composite and a reconstructed one. The repaired variable-presheaf
   argument keeps the supplied original middle map literal, proves its value using
   the same chosen biproduct comparison, and composes the original target equality
   before native specialization. SecondSquare passed in88.120485s.
5. **Reconcile actual local policies and interface heads.** The split facade had lost
   the original three file-local options: `backward.defeqAttrib.useBackward true`,
   `backward.isDefEq.respectTransparency false`, and
   `backward.isDefEq.respectTransparency.types false`. Imports do not inherit them.
   Their exact restoration was baseline-input reconciliation, not a new allowance.
   Earlier missing-policy facade failures remain actual failures, but do not test
   the original policy or identify a unique kernel cause. Restored-policy v15 still
   failed; a bounded stage diagnostic reached the body/exactness, not the completed
   five-lemma application. Splitting into [the pinned Mathlib five-lemma proof’s two four-lemma arguments](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Algebra/FiveLemma.lean#L212-L221) and
   narrowing their side-property inputs retained the same mathematics. A later
   diagnostic accepted supplied module objects but failed while matching actual
   maps. The final native calls therefore let the existing LinearMap four-lemma
   interfaces infer endpoints/actions from the actual arrows. Surjectivity then
   exposed the precise boundary-square mismatch: the square names the public
   `structureOpenKunnethBoundary`, whereas the caller supplied its raw implementation.
   Both calls now retain the public arrow literally; only injectivity's source
   exactness links unfold its one original definition. Both native branches,
   facade and actual consumers passed.

The experimental Gluing/GluingFour wrappers are omitted from final admission because
none of their four declared symbols has an actual production/test consumer and they
register no instances, simp rules or automation. Their only remaining role was to
forward the pinned Mathlib five-lemma import. This conclusion is based on symbol and
registration inspection, not merely on a redundant import edge. Their exact passed
sources and failed-specialization contexts remain in the case evidence.

## Diagnostic corrections and limits

Nested profiling substantially perturbed the original cup proof: an instrumented
180s timeout was followed by the identical original body passing unprofiled in7.813
frontend seconds (12.599996s overall). The cup-bottleneck attribution was withdrawn;
the original cup proof was retained. Other profiled57/82/99/180s observations remain
diagnostics only; absent thresholded frames do not mean zero cost.

Earlier zero-output prefixes did not locate a proof phase. Tiny ordered controls
found invalid String `+` marker syntax; a literal core control passed and showed
stdout captured as JSON `information`. An import fixture reached ENTRY and then
failed an independent header linter; that observation was reused without a separate
clean-import certification. An initial file marker failed on an IO-error throw in
CommandElabM; the corrected append/flush control passed. Subsequent constant file
markers identify reached source/tactic commands, not asynchronous kernel completion.
Failed, timed-out, unrun and recovery markers remain separate from CPP acceptance.

A real disk-admission hold interrupted the work. Only exact authorized, backed-up
own transport/log duplicates were removed by the native owner; sources, `.lake`, CAS
and proof caches were preserved. The10GiB hard reserve remained intact. A prior extra
1GiB was a planning work/growth allowance, not a second hard reserve. Fresh resource
recovery allowed v8 onward to proceed. No source result was inferred from cleanup,
a source capture, a queue event, a tool hook, a worker return or mathematical review.

## Evidence and reproduction

- `baseline/` preserves original source, public signatures and the successful
  monolith event with the cancelled-parent boundary.
- `sources/`, READY files, `ACTUAL-RUNS.json`, `LATE-ACTUAL-RUNS.json` and
  `CONTINUATION-RUNS.json` bind source images and completed native events.
- `diagnostics/` preserves the bounded probes, exact options/setup projections,
  raw errors and marker results. `HISTORICAL-CONTINUATION.md` retains then-current
  observations without treating them as final status.
- `RAW-EVIDENCE.json` records six larger raw traces and setup files by original
  locator, SHA256 and byte count. They are not included in this compact case.
  The corresponding local probe results, receipts and setup summaries retain
  the reported outcomes and input identities. Direct inspection of full profiler
  output or setup bytes requires the external originals; their locators are
  provenance, not portable case links. No claim about unobserved profiler frames
  or a unique cause follows from the compact records.
- `FINAL-READY.json` and `FINAL-PUBLIC-CORRESPONDENCE.json` bind the final15-source
  import-minimal candidate and the explicit v19/final-import coverage distinction.

Use the selected library's ordinary prepared-cache build, with current owner/control
and actual changed-input selection. For example:

```sh
lean-tools build --root /absolute/coherent/aglib --state /absolute/fresh/logs \
  Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethOpenMayerVietoris \
  Aglib.AlgebraicGeometry.Cohomology.StructureSheaf.Kunneth \
  AglibTest.AlgebraicGeometry.Cohomology.StructureSheaf.KunnethOpenMayerVietoris
```

Recover compatible existing outputs and check actual gaps; this case does not request
an unchanged monolith, whole-library rebuild, kernel replay or separate client chain.
Current operating guides own commands and final checks. Root owns the actual-main
source admission, final changed-import check, generated entries, review, Git and
publication decision.
