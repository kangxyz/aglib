# Continuity: use the original value at its typed native endpoint

## Question, source basis and scope

This is one supporting application of the existing typed-endpoint,
original-value and exact-dictionary methods. It records two related continuity
caller repairs from the fixed [C1 manifest](C1/manifest.json) and
[C2 capsule](C2/capsule.json). The latter's original SHA256 is
`15de7530963a7e2e45a9da6f0e1721d1cee3956ada08f8f467de9b17bfb42639`.
Native HEAD is `54d6974ace11bf7d197aa925cb8cade86db8a24f`, Lean 4.34.1,
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
The [source capsule](source-capsule.json) binds all small copied sources,
deltas, packets, ordinary review records and closed receipts/logs/events to
their exact original locations and hashes. Large whole-SOURCE manifests stay
at their durable hash-bound R locations listed there. Absolute paths inside
unmodified historical packets are provenance; the links in this case are relative.

The product records implementation correspondence and actual compiler outcomes.
It neither supplies a new mathematical verdict nor changes mathematical status.
The [C1 result](C1/RESULT.json) and [C2 result](C2/RESULT.json) retain their
own conditions, source vectors and review boundaries.

## C1: the original coefficient component and colimit leg

Failed Stalk source [907f](C1/failed-stalk-907f.lean) is the immutable v6
`Stalk.PullbackLimitCoefficient`. Its [feedback](C1/failed-stalk-feedback.txt)
records a line-length error, a residual reflexive transition-map goal, and a
line-156 rewrite failure at the original insertion equation. The compiler's
implicit-transparency diagnostic displays the mismatch between literal
`C.obj i` and the inverse-image composite object. This describes the reported
failure boundary; no exact kernel reduction pair or compiler defect is inferred.

Final [fdbf](C1/passed-stalk-fdbf.lean) retains the original public insertion
target. The [repair](C1/stalk-repair.diff) types a local equation with the
original `pullbackConeCoefficientComponent.inv` at literal `C.obj i`, composes
`constantDiagramColimitIso_ι` with `congrArg Iso.inv` of the proved original
component equality, and supplies that whole value law by `exact`. The residual
normalized map equation closes by `rfl`; formatting is repaired. The fixed
coefficient, actual diagram/System, image functors, triangle maps, apex cocone,
colimit and insertion values remain original. No new comparison model or
desired-law premise is inserted. The original header is retained in
[original-Stalk](C1/original-Stalk.lean), with its header correspondence in
C1's manifest.

The related Root consumer is a separate module,
`Stalk.PullbackCohomologyNormalization`. Its failed [b36](C1/failed-root-b36.lean)
bytes come from immutable `native-colimit-leg-normalization-staging/versions/v1/after.lean`.
The mutable top-level `after.lean` now contains 3fb and is not relabeled b36.
The [Root feedback](C1/failed-root-context.txt) records `rw` failing at line43:
the original diagram cohomology input and native `Sheaf.H` input did not match
at implicit transparency, with `Shrink` reported unexposed.

Final [3fb](C1/passed-root-3fb.lean) names the original pullback value `z` at
`H.{e}(C.obj i) n`, applies native `Sheaf.H.map_comp_apply` directly, and
composes `congrArg` of the original insertion law with an explicitly typed
arrow. The [delta](C1/root-repair.diff) preserves the complete theorem header,
cohomology source, input and maps. Root's proof and pass do not stand in for
Stalk coverage.

## C2: the original HasExt dictionary and integer-source transport

Failed Connecting [3905](C2/sources/old-39056a2e-Connecting.lean) exhausted the
default typeclass budget 20000 at the projected `Functor.const` cone-apex
`HasExt` goal (51:2), then the default conversion budget 200000 at the original
inverse-constant source-map lambda (73:14). The [diagnostic](C2/old-3905-diagnostics.log)
retains both errors. Companion Exact `6ce27e8c` was unreached; it has no own
failure verdict from that request.

The [v7 repair](C2/3905-to-5d16.diff) supplies the already given
`HasExt.{e} (AbelianSheaf c.pt.unop)` via `inferInstanceAs` at the exact
projected apex type. It pins the original stage/apex categories and objects.
`diagramIntegerConePrecomp` names the original inverse constant-source arrow
at the actual `diagramIntegerSystem.obj` endpoint; its body reduces only the
existing `System.ofLeft` object presentation before returning the same
`inverseImageConstantIso.inv.app` on `ULift ℤ`. Both existing generic colimit
assemblers receive that same typed original arrow. The generic proof and
original alpha, tau, delta and comparison maps are preserved.

Intermediate Connecting [5d16](C2/sources/intermediate-5d161d21-Connecting.lean)
removed those earlier diagnostics but failed the enabled style linter at60:2:
use `let`, rather than `letI`, in Prop. It did not pass. Final
[58c2](C2/sources/final-58c287bb-Connecting.lean) changes only that binder;
the [v8 delta](C2/5d16-to-final-58c2.diff) does not change its dictionary value
or premise. Companion [Exact680a](C2/sources/final-680af1fe-Exact.lean) uses the
same typed source alias and explicit apex category, as the
[Exact delta](C2/unreached-6ce27-to-final-680a.diff) records.

Independent stage/apex/index/Hom worlds and the original Ext world `e` remain.
The original `HasExt` hypotheses, pointwise monic eta, cartesian representing
source, exact additive left functors and actual-shaped colimit assumptions
remain. No enough-injectives assumption, artificial universe equality, new
cohomology model, source carrier, comparison arrow or desired-law premise is added.

## Actual closed native coverage

The three caller requests below used jobs2, threads4, 12800 MiB/frontend,
32768 MiB/run and no CPU oversubscription. Source keys name whole captured
cohorts, not isolated files. All listed receipts have closed groups and no
input drift. Standard declaration200000/typeclass20000 budgets remain, with
no added production option, suppression or flag.

| Request prefix | SOURCE prefix | Own result | Shared exit |
| --- | --- | --- | --- |
| [960222c1](evidence/remote-960222c105fb4095b940a5117ede023c/receipt.json) | `a253e6ed` | Stalk907f failed (379s); C2 Connecting3905 failed; Exact unreached | 1 |
| [18bae28d](evidence/remote-18bae28d3d084929b9ec85394374e177/receipt.json) | `660b69e6` | Stalkfdbf passed (353s); Rootb36 failed (7.8s); Connecting5d16 style failure; Exact unreached | 1 |
| [d428d600](evidence/remote-d428d60042ce45b8abdf7914143ee304/receipt.json) | `56d82351` | Root3fb passed (11s); Connecting58c2 passed (118s); Exact680a passed (95s) | 0 |

These seconds are whole frontend/module observations. The 379s failed Stalk
and 353s successful Stalk are neither per-tactic costs nor a matched speedup.
Root7.8/11 is a separate module context, and C2's 118/95 observations concern
two different files. Cached contexts, sources and root cohorts differ; exact
profiles are bound per run rather than generalized across packets.

C2's exact current four-file pass matrix is retained in its
[compiler result](C2/compiler-result-all4.json):

| Current source | SHA256 prefix | Actual pass run | Shared exit |
| --- | --- | --- | --- |
| RepresentedDiagram.ExactSequences | `5c73f898` | [e55fbe2f](evidence/remote-e55fbe2f23ba424681e50f9ecbcccc3c/receipt.json) | 1 |
| DiagramCokernelTransitions | `318544c5` | [960222c1](evidence/remote-960222c105fb4095b940a5117ede023c/receipt.json) | 1 |
| DiagramCohomologyConnecting | `58c287bb` | [d428d600](evidence/remote-d428d60042ce45b8abdf7914143ee304/receipt.json) | 0 |
| DiagramCohomologyExact | `680af1fe` | [d428d600](evidence/remote-d428d60042ce45b8abdf7914143ee304/receipt.json) | 0 |

The two lower passes are retained source-matching coverage; the later request
need not rerun them. Their full source snapshots are in `C2/sources/`, and
C2's original capsule binds each file to its source manifest, receipt and
event record. The e55f request also used jobs2/threads4/12800/32768 with no
oversubscription. A successful file inside shared exit1 retains only its own
scope. Stalk's success inside 18bae does not turn that shared request into a
success, and d428 does not recreate the earlier Stalk pass.

## Reusable method and mathematical boundary

At a native wrapper, bind the supplied property or source at its exact actual
endpoint before inference crosses an opaque or semireducible presentation.
Keep the same original value: compose the whole original typed component/leg
law or apply the native cohomology law directly to its typed argument. Expose
an existing dictionary with `inferInstanceAs`; use one alias for the original
source arrow where two assemblers need it. Retain matching incremental passes
and repair the actual remaining style/type boundary. These are applications
of [typed comparisons](../../../PERFORMANCE.md#conversion-boundaries) and
[exact dictionaries](../../../PERFORMANCE.md#instances-and-universes), not a
new universal performance rule.

The [ordinary C1 review](review/continuity-cone-constancy.md) retains its fixed
v2 derivation, withdraws the old v1–v3 literal helper-signature claim, and
records restoration at generic482. It separately accepts Root3fb's typed
proof hunk against the original injection theorem. It explicitly did not
inspect final Stalkfdbf; the compiler pass supplies final-source execution,
not an expanded ordinary review. Its then-pending Root native statement is
historical and is superseded only by the matching d428 pass.
The [ordinary C2 review](review/continuity-ext-exact-sequences.md) retains the
fixed v5 proof verdict. Later generic/native dictionary, typed-arrow and Prop
binder edits are not relabeled as an independent v8 review. Author results
record unchanged mathematical objects, arrows and conditions. Production
validation here does not close mathematical acceptance obligations.

## Evidence use and limits

Every copied file is hash-bound in the capsule. `C1/` holds complete failed
and passed sources and their exact diffs; `C2/` holds the failed/intermediate/
final caller sources, retained lower sources, exact diffs and diagnostic
excerpts. `evidence/<full-run-id>/` holds unmodified receipts, logs and events
for all four runs. The packet's large SOURCE manifests remain in R with
exact paths and hashes rather than duplicating whole-library data.
For source reconstruction, apply each `.diff` with `patch -p0` to a disposable
tree matching its recorded header paths and compare with the saved afterimage
hashes; the snapshots themselves need no patch replay for inspection.

The final recorded command was `lake --rehash build
Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramCohomologyConnecting
Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.DiagramCohomologyExact
Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PullbackCohomologyNormalization`
on the matching prepared dependencies. Earlier full commands, executable/config
fingerprints and observed outcomes remain in the receipts. Current operating
guides own future commands.

The operational result is compilation of the corresponding original objects
at default budgets. There is no controlled wall/RSS/energy improvement,
per-tactic timing, ablation, unique causal conversion pair, exact kernel
reduction pair, compiler-defect verdict, whole-library/whole-continuity closure,
or standalone final lint/test/audit/replay claim. No new compilation, profile,
benchmark, source inventory or acceptance chain was run to write this case.
