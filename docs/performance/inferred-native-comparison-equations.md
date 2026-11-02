# Consume the original inferred equation before component cancellation

The original proper module-derived base-change component passed in a frozen
Lean context after the proof retained the producer application's actual inferred
equality and fed it directly to a complete two-category cancellation lemma.
Manually restating that concrete equality had timed out. This records a bounded
repair and its diagnostic history, not a matched speedup or a unique compiler
cause. The later generic framework module also passed in the ordinary production
checkout; the thin Scheme consumer's production integration remains pending in
this evidence snapshot.

## Mathematical target and preserved conditions

The target is `properModuleDerivedBaseChange_isIso_of_torsion_homology` for
`((moduleDerivedBaseChangeMap Λ f f' g g' sq.w.symm).app K)`. Here `Λ` is an
arbitrary ring in `Type (u + 1)`, `f` is proper, `sq` is the original Cartesian
square, and the given `K` is bounded below with internally torsion homology in
every degree. The four actual module-derived worlds remain independently
supplied. Each of four proof-only abelian derived worlds is selected once,
locally, by its standard realization. No common annihilator, geometric bound,
new model, extra cube hypothesis, or assumption that scalar forgetting preserves
injectives is introduced.

The proof uses the original torsion comparison, the abelian proper-base-change
theorem at the same underlying object, the exact original six-transformation
mate cube, the four actual comparison isomorphisms, and conservativity of the
original derived underlying functor. It proves invertibility of the original
module exchange; an arbitrary isomorphism with the same endpoints is insufficient.
These mathematical descriptions come from the supplied author's correspondence;
this documentation does not supply independent mathematical acceptance.

## Method and actual implementation

Keep the application unannotated at the concrete producer boundary:

```lean
have hcube := moduleDerivedBaseChangeMap_underlying Λ f f' g g' sq.w.symm K
```

Prove the complete cancellation over variable categories and arrows. Its interface
keeps the original arrow `β` in the conclusion:

```lean
{C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)
{M N : C} {P A B Q : D} (β : M ⟶ N) {a : A ⟶ B}
(u : P ⟶ A) (v : B ⟶ Q) (s : P ⟶ F.obj M) (t : F.obj N ⟶ Q)
(h : u ≫ a ≫ v = s ≫ F.map β ≫ t)
(ha : IsIso a) (hu : IsIso u) (hv : IsIso v)
(hs : IsIso s) (ht : IsIso t) (hF : F.ReflectsIsomorphisms) : IsIso β
```

The helper installs the supplied dictionaries, obtains invertibility of
`s ≫ F.map β ≫ t` from `h`, cancels `s` and `t`, and reflects invertibility
through `F`. At the native call, provide the original `F`, `β`, `u`, `v`, `s`,
and `t`, then pass `hcube`. Let this actual equation infer the abelian exchange
component `a` and its endpoints. Prove its invertibility from proper base change
and torsion transfer, prove the four edge facts from the original comparisons,
and supply actual conservativity. Do not first coerce `hcube` to a manually
rebuilt native equality.

The complete generic proof was moved with identical binders and body into
`CategoryTheory.isIso_of_component_equation` in
`Aglib/CategoryTheory/Adjunction/Mates/UnitIsomorphism.lean`. The Scheme owner is
`Aglib/AlgebraicGeometry/EtaleCohomology/Exceptional/Derived/ProperBaseChange.lean`.
The existing unit theorem and the producer `UnderlyingBaseChange.lean` were
unchanged. The [retained correspondence and source snapshots](cases/inferred-native-comparison-equations/README.md#raw-metadata-and-correspondence)
record this move and the full actual application; the signature above is an
interface excerpt, not a standalone source file.

`proofConclusion` was a diagnostic device for naming the proposition inferred
from a real proof application. Production consumes `hcube` directly. A `True`
conclusion, unused proof, increased budget or disabled linter is not this repair.

## Failed approaches and diagnostic progression

Three production attempts all failed at the default kernel budget:

| Source SHA-256 prefix | Approach | Observed failure |
| --- | --- | --- |
| `93b45985` | Concrete component cancellation in the public proof | Public theorem `47:8`; reported module 98 s |
| `facac44d` | Generic whole-cube cancellation, then concrete specialization | Public theorem `69:8`; reported module 100 s |
| `4eaeb3d9` | Private pointwise proof over variable abelian data, then standard public specialization | Private theorem `66:16`; reported module 106.5 s; unknown-private-constant cascade |

The [original evidence, exact commands, sources and full logs](cases/inferred-native-comparison-equations/README.md#original-production-failures)
retain each failure and its distinct production profile. Neither a passing
provider nor the absence of a helper error made the failed consumer pass.

The frozen diagnostic sequence then separated these boundaries:

1. Faithful proposition formation and actual prerequisite proof values passed.
   Concrete full and mapped cancellation still timed out; standalone reflection
   produced no error. Whole comparison `IsIso` values also passed, but supplying
   all facts or whole isomorphisms did not repair assembly.
2. Fixing categories, functors and comparisons passed; fixing actual exchange
   values exposed failure. Fixing the module exchange alone produced no error;
   the actual abelian exchange still failed even with all functors explicit.
3. Complete two-category morphism assembly passed, including the actual abelian
   component with supplied or inferred invertibility. Those probes were
   conditional. The original cube proof value passed, while checking its literal
   application against the manually restated pointwise equality timed out.
4. Raw type extraction found all twelve native constant functor heads. The
   proposed eta-expanded/record-head explanation was ruled out for that producer.
   Eight optional module builders were incomplete; their false flags are not
   mismatches. Earlier tooling errors and partial extraction remain failures.
5. The original aligned raw type pair was 71,343 bytes / 1,248 nodes (actual)
   versus 100,900 bytes / 1,844 nodes (manual expected). Its first syntactic
   difference was a `WEqualsLocallyBijective` proof argument inside
   `SheafOfModules.instAbelian` under `DPlus`. This is a raw observation, not a
   definitional-inequality verdict or unique explanation of kernel cost.
6. The local-W value control still timed out. Early and late W-scope captures
   changed the expected `HasDerivedCategory` binder domains relative to the
   producer and stopped strict matching at binder 6. No genuinely aligned new
   pair was obtained. Explicit typing at the two underlying projections removed
   namespace errors but still left a kernel timeout. Those approaches are not
   repairs; the author's source-typing proposal remains tied to its own phase.
7. The inferred-proposition sequence was `bac918c8` (Prop-valued definition lint),
   `58c6c2fc` (unsupported theorem header hole before kernel checking),
   `d4068930` (private helper in a public header), then `1dd654bd` (public
   actual-proposition helper, whole diagnostic pass in 4.761083 s). The first
   three are not kernel-negative results; the fourth is not the full theorem.
8. Full source `5d7d253d` retained inferred `hcube`, discharged every original
   fact, and passed in 6.536038860678673 s in that frozen context.

The exhaustive [26-record diagnostic/setup table](cases/inferred-native-comparison-equations/README.md#diagnostic-and-setup-sequence)
keeps failed, partial, setup-only, type-only, conditional and full-source outcomes
separate. Raw pairs, contexts, projections, scripts, requests and executed source
versions are retained with hashes. Files explicitly named unexecuted remain
unexecuted; they acquire no coverage from adjacent successful runs.

## Versions, resources and evidence boundaries

The source checkout HEAD is `54d6974ace11bf7d197aa925cb8cade86db8a24f`, with
Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
The recorded normal heartbeat budget is 200,000. Frozen candidate runs used
jobs 2, threads 4, Lean heap 12,800 MiB and RSS 32,768 MiB, with
`autoImplicit=false`, `warningAsError=true`, the standard Mathlib linter set and
long-file limit 1,500. Initial production profiles are retained separately.
No repair changes transparency, budget, axioms or native linter controls.

| Evidence identity | SHA-256 / run |
| --- | --- |
| Frozen provider source | `65bc75bd87f6942ed330fbc8ccfc98bdf61a14989f0b422a98d87f9a64e91ef7` |
| Frozen setup | `922034a0e8a01bed3cdcc4a09ed1ab37d1fd5b7f6b15d5a3f26e1c8d58a250f5` |
| Frozen provider artifacts | `b8a81d3f1d55c994c43b511c84dec652f6367b2ff9a0ad34d1f9a153192e3bf6` |
| Full frozen source | `5d7d253d40622574dd66111024c0a67c388c238cc25f33d8cecd4019a3592111` |
| Full frozen pass | `remote-2e13005a9ced49f9957f5f02c7754e8a` |
| Changed generic source | `f2b0fba00d9c04af59cebfd655491a9af2084e0c9baf437e25ec48883efb9933` |
| Generic ordinary production pass | `remote-274bb8825e4046c88f4f9d65569bd948`, one frontend, 3.286 s |
| Thin Scheme source, production integration pending | `7f7ddd67dbab5b61f062332dc01e99b4d6c4a9c8d6531a465ab08f554bddf9f4` |

The generic run's build log reports 1.8 s for the module; the supplied 3.286 s
frontend observation is a different timing field. The frozen pass is retained
argument coverage on its original dependencies. It is not relabeled as current
Scheme integration or global R4/P6 closure. The thin Scheme consumer and remaining
P6 chain await matching H1 imports in the supplied snapshot. Independent affected
mathematical review remains with the principal and reviewer; no accepted or
established status follows from this case.

There is no matched before/after speedup, identified unique reduction pair, or
whole-system improvement. Conditional probes do not supply production hypotheses.
Raw dictionary differences alone do not justify replacing model data or global
instance priorities. Historical failed checks remain failed. Approval rejections
before process start are not compiler failures. No global étale, six-operation,
torsion-target, composition, Gamma or Nagata closure is asserted.

## Retention and reproduction

The [self-contained evidence index](cases/inferred-native-comparison-equations/README.md)
links every retained source, failed approach, decisive log, receipt, patch and raw
projection. Its relative SHA-256 manifest binds these copies; original JSON
retains historical absolute paths, resolved locally by `LOCAL_PATHS.json`.
Caches, compiled binaries and unrelated large artifacts are excluded.

For a local integrity check from this checkout, without invoking Lean:

```sh
python3 - <<'PY'
from pathlib import Path
import hashlib, json
p = Path('docs/performance/cases/inferred-native-comparison-equations')
for name, item in json.loads((p / 'SHA256_MANIFEST.json').read_text()).items():
    data = (p / name).read_bytes()
    assert len(data) == item['bytes']
    assert hashlib.sha256(data).hexdigest() == item['sha256'], name
print('All retained evidence hashes match')
PY
```

Exact historical argv, candidate bytes, cwd/profile information and result codes
are in the retained run index, requests, results and receipts. Re-execution needs
the admitted broker-controlled environment and matching frozen providers; the
source/log archive alone does not recreate the cache. Ordinary production uses
the existing incremental target/consumer graph (the recorded generic command was
`lake --rehash build Aglib.CategoryTheory.Adjunction.Mates.UnitIsomorphism`).
Recording this case ran no compiler, benchmark, replay, lint or axiom cycle.

## Integration milestone: 2026-10-27, source 33013d99

The earlier pending statements above describe the initial documentation snapshot.
The later ordinary native run `remote-c2c602c4e4e243d09be4b250ca35d3f0`
passed the exact thin Scheme source `7f7ddd67` with generic source `f2b0fba0`
on source capture
`33013d99bfd1b9f804c6cffd93496a4f9aec1ffbb57645d4925f4f61e61dcf70`.
The run closed with exit 0, no input drift, and all 257 fresh frontends passing.
Two previously failed providers had been repaired before this successful run.
This supersedes the pending thin-R4 integration limit only for this snapshot;
it does not revise the historical frozen `5d7d253d` 6.536 s or generic-module
`f2b0fba0` 3.286 s observations.

Lake displayed 5.9 s for the R4 leaf; its observed compiler interval was
5.272646561264992 s. The whole native execution took 1618.6432044357061 s,
including required imports. That whole-run duration is not the R4 proof time.
These are distinct recorded metrics, without a matched speedup comparison or
unique conversion-cause claim.

The independent fixed changed-proof review accepted mathematical and source
correspondence for the exact `7f7ddd67` / `f2b0fba0` pair on its identified native
prerequisites. Its report predates this integration run and correctly retains
its then-pending execution limit. The later run supplies separate source-bound
compilation coverage; neither result assigns established status.

A later intrinsic-higher native source wave is active. This pass does not grant
permanent coverage to subsequently changed imports. The five downstream P6
endpoints and the separately owned first compatibility failure remain pending;
no whole-étale or six-functor closure follows. Defaults, mathematical premises
and original maps remain as described above. This documentation update launches
no compiler, test, benchmark or replay cycle.

The [integration evidence addendum](cases/inferred-native-comparison-equations/README.md#integration-milestone-2026-10-27-source-33013d99)
retains the exact report, source manifest (SHA-256
`4948d610076288f421cdb8fe6f2a64136ce720c5431832c4bab67cc56c22cee9`),
receipt, build log, compiler events, updated author packet and fixed independent
review. Existing retained source snapshots match both target hashes in that
manifest; no unrelated source archive is duplicated.

## Field follow-up: infer the composed equality before normalization

The later native production Field pass now validates the selected minimal proof
on its actual source capture. This is a separate follow-up to the R4 inferred
equation method. All earlier R4 history and its source-33013 milestone remain
unchanged; isolated candidates retain their original scope.

### Source and method

The native theorem `comparison_torsor_representative` in
`Aglib/AlgebraicGeometry/EtaleCohomology/Kummer/Field.lean` compares the original
Kummer field comparison on a torsor representative with the class of the original
Galois cocycle. Preserve the actual field, coefficient action, marking, units,
positive generators, finite-etale/Galois hypotheses, `hA`, `hR` and `HasExt` worlds.
The minimal proof changes only the final handling of the existing equations:

```lean
have hfinal := hmap.trans hclass
simp only [comparison, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
  fieldCocycle] at hfinal ⊢
exact hfinal
```

Infer the composition without an expected target first. Normalize that inferred
hypothesis and the actual goal in their respective locations, then apply the
normalized equality. Earlier `simpa ... using` forms repeatedly encountered
recursion limits or type mismatches with identical printed expressions. Those
printouts do not prove agreement of all hidden arguments, and their differences
do not identify a unique compiler cause. No shared helper, constructor, new
model, import, public premise, map, universe, budget or production option is
introduced. The unused conditional SquareTransport extension is not adopted;
its native source remains `926601b0…`.

### Distinct evidence and limits

| Observation | Actual source and result | Scope |
| --- | --- | --- |
| Original native Field | `616b87a1041f6eed9b19b5d5ecd0bc50c3df4acf636496f42b7c4800883c35ce`; failed production run `remote-bf20009e4ff941a2affe91985903532b` | Historical failure, not repaired by relabeling a probe |
| Minimal inferred composition | Candidate `1de5eb6705762fed19b3c648cb5b962117e1a0f3a79011b432fe7fa0df138257`; `remote-1629cb74b6c74f928ec4dbbb203a09f0`, source `0329c470c50cbd8465e64908f2f2560c8a8e90dd28ce8227db0b4a4331ec3c62`, setup `9e447e6b…`, exit 0 | Faithful isolated original Field prefix/candidate, one frontend; native production remained unchanged in that run |
| Logger-free whole-factorization proof | Candidate `5bbebaa438fc86e11cd9e6bc87eb16af223710c941a257ffc0bde44e099284f9`; `remote-dd2ccbe6f9dc4ee784aaafdc85ae74cb`, source `1fc29d52148d1cd89f2c66eb71592090b2ff9f9fa90721abe931f372d79bdc3d`, setup `8a299ce5…`, exit 0 | Separate faithful isolated candidate, reported 130.414 s; no production/root adoption in that run |
| Minimal production adoption | `production-v7/READY.json`, SHA-256 `d08304729d0b3d19915f3af0db30d6ad3653c66268d07f303769452458936d9f`; exact `1de5eb67…` after `616b87a1…` | Source application guarded by HEAD/status/preimages; Field and curve roots were pending at adoption; later Field result below |

The minimal isolated record reports 124.17859371006489 s elapsed; the supplied
approximately 123.7 s compiler observation includes the native prefix. Neither
is proof-only time, a global performance result or a matched before/after
speedup. The whole-factorization candidate's 130.414 s likewise includes its
actual isolated source. These two different runs are not interchangeable.

Earlier Meta DATA probes had syntax, evaluator and hygiene failures; they do
not establish a hidden-argument diagnosis. The `e85d1bfa…` candidate exited 1
with only the unused `run_tac` logger linter error. That is not a whole-file pass
or a compiler-cause verdict. The logger-free `5bbebaa4…` observation is separate.
Unexecuted route projections retain their historical unexecuted labels; later
execution is bound to its actual request, candidate and receipt. Sources,
requests, exact command records, complete logs, failed route patches and
configurations are retained in the [Field evidence index](cases/inferred-native-comparison-equations/field-followup/README.md).

### Native-option faithfulness and withdrawn interpretation

The interpretation that A's raw no-build scratch probes were equivalent to the
native Aglib option environment was **withdrawn**: those probes omitted Aglib's
library options. Their results remain observations on their actual setup and
must not be used as native-option-equivalent evidence. Actual native production
evidence is unaffected. The exact amended A input records are `global-square-formation-input.json`
(run `remote-9971871b51874eee85fb256b97040c89`),
`coordinate-value-formation-input.json`
(run `remote-b3b1c7fb64f1440896052e3cc7f0b6f1`), and
`constant-group-square-full-probe-input.json`
(run `remote-6ade13625ede4848945b82209e3f27c3`). Each records
`native_library_options_forwarded=false` and
`native_option_equivalence_withdrawn=true`; scratch argv lacked native
`--setup` and per-library `-D` flags. The complete raw effective option map
was not separately recorded. These exact metadata files are retained.

For faithful native probes, obtain the setup using the official
`lake --no-build setup-file actualModule` route and invoke Lean with `--setup`.
Retain the exact native module `name`, `isModule`, full per-library options and
imports. `C-Field-native-options-verification.json` mechanically compared the
complete Aglib options: `autoImplicit=false`, `warningAsError=true`, standard
Mathlib linter set, long-file limit 1500; it also retained existing local source
options. It did not claim a bytewise comparison to the unavailable original
production IR setup, nor a production pass. Existing native local options are
preserved, not introduced as a repair. The pinned Lean 4.34.1 / Mathlib `d13f23…`,
normal 200,000 proof budget and default recursion limit remain unchanged.

### Actual production milestone and remaining coverage

The exact adopted Field source is
`1de5eb6705762fed19b3c648cb5b962117e1a0f3a79011b432fe7fa0df138257`,
matching the guarded `production-v7/READY.json` and the actual source manifest
SHA-256 `f728559a3a59f5675fdb0815d1f0149631763528dd94e43e370208859b9cb613`.
Production run `remote-012592f60c0140bcae45c12e6ba60d6b` used source capture
`1d0b5938b40716e5f90a1e63eac08ab11c5e0db6e0c55d274964b875f1a36c74`.
Field's frontend exited 0; Lake displayed 122 s and its observed compiler
interval was 122.4589021652937 s. These module observations include the
source prefix; comparison with isolated 123.7/124.1786 s or 130.414 s is not a
controlled speedup or proof-only comparison.

The shared run closed with no input drift, 21 fresh frontends, 20 passing and
one failing. Its overall exit 1 was the unrelated P6 ModuleMate failure; it
neither retracts the source-matched Field pass nor supplies a whole-graph pass.
The three curve entries were not selected because their actual closures reach
the separately owned pending/failed Global producer. Full C56 and those entries
remain pending; no whole-refactor, global étale or established-status closure
is asserted.

The native profile was jobs 8, threads 4, Lean heap 12,800 MiB, RSS cap 65,536 MiB;
Lean 4.34.1 and the same pinned Mathlib and native library/source options remain
in effect. The exact Lake command, source identity, receipt, full log, events,
adoption guards, original and repaired Field sources, failed routes and setups
are linked in the retained Field evidence index. The two isolated successes
remain separate from this production observation. No new helper, model, import,
option, public premise, budget or map was introduced, and no unique hidden-argument
or compiler-cause conclusion is drawn. Documentation delivery ran no compiler,
tests, lint, benchmark, replay or separate client cycle.


## Global follow-up: shared construction and normalized proof inputs

A later represented-restriction repair builds the complete operational H/K/c
family once before constant representation and normalizes actual object and
constructor projections in the instantiated core telescope and original proof
inputs. It preserves the economical raw equation and original maps and values,
without a new reference model or desired-equality premise. The normal full
Global restriction module passed on source `998a4a2e`; the trace-instrumented
V35 scratch run failed only on diagnostic trace lints and is not the pass.
The [Global supporting case](cases/inferred-native-comparison-equations/global-followup-20261029/README.md)
retains exact source identities, failed variants, counter qualifications and
the full production receipt. The two Proper endpoint dependency closures still
reach a failed Kummer module; this is not a proper base-change or whole-theory
completion.


## Continuity triangle follow-up: preserve original proof inputs

Build whole laws from the same original comparison heads, then use raw
evaluators over independent category and morphism worlds. Normalize only the
necessary definitional views in the instantiated producer and original equality
proof-input types before supplying the original values. In this case `simp`
had changed two equality proof inputs to `True`; `dsimp` preserved the required
equality types. The independent ordinary review passed the exact eight-source
closure under its original hypotheses, and the native triangle module passed
on source `71a5a26b`. The mixed production build itself exited 1 on a
separate dependency; the seven other passes are retained on their producing
bases. The [supporting case](cases/inferred-native-comparison-equations/continuity-triangle-followup-20261029/README.md)
records the original failed source, the header-lint-only formation probe, the
failed proof-input applications, the complete evidence and review boundaries.
No matched speedup or unique compiler cause follows.


## Proper injective follow-up: retain the original single head

When a native adapter timed out at kernel checking, the complete lower
assembly was retained and a lower corollary exposed the variable original
single functor `Z` with its literal construction equation `Z = U ⋙ single`.
The native call supplies the actual `zmodSingle` and `rfl`, keeping the same
coefficient head in the input and conclusion. The independently reviewed
source repair and both changed modules passed on source `c07d5419`. The
[complete supporting case](cases/inferred-native-comparison-equations/proper-injective-followup-20261029/README.md)
retains the earlier failed source, its separate aggregate errors, full
production evidence, original conditions and review boundary. This does not
claim a matched speedup, unique compiler cause, or broader Proper completion.
