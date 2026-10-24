# Lean compilation performance

This guide distills the reusable methods and decision process from the retained
[case records](performance/README.md). Read a relevant case for its original
conditions, failed approaches, measurements and evidence. The complete records
remain saved independently of this synthesis.

## Find a method

| Observed problem | Method |
| --- | --- |
| Concrete maps, values or dependent transports are costly to compare | [Conversion boundaries](#conversion-boundaries) |
| Generic proof passes but specialization, a field or a short `rfl` is expensive | [Shared constructions and equations](#shared-constructions-and-equations) |
| Instance-search limits, universe `max` or incompatible parent structures | [Instances and universes](#instances-and-universes) |
| Rebuilds, overlapping jobs, memory, checker startup or import-only failure | [Build-and-check costs](#build-and-check-costs) |
| An explicitly requested investigation of cause or timing | [Requested diagnosis and evidence](#requested-diagnosis-and-evidence) |

## Repair workflow

Use these decisions within ordinary proof iteration:

1. Locate the failing phase from existing feedback: cache/input preparation,
   imports, elaboration/instance search, tactic work, kernel checking, checker
   startup or serialization. A short proof or completed tactic can still leave
   expensive kernel conversion.
2. Read the relevant method below and its matching case. Check the actual
   source, toolchain, structures and budget conditions; consult the dependency's
   cases when it owns the expensive construction.
3. Choose a bounded repair at the implicated boundary, retaining the original
   mathematical objects, maps, hypotheses, universes and reduction interface.
   Keep package defaults and any necessary documented finite local allowance
   under the [existing budget policy](DEVELOPMENT.md#setup-and-focused-builds).
4. Compile the affected leaf incrementally and include actual in-package
   consumers when their interface or cost is implicated. Keep compatible
   artifacts and successful checks; repeat only changed inputs, failures and
   actual coverage gaps.
5. If the recorded methods do not cover the problem, use
   [upstream reference search](#search-upstream-references). Separate profiling,
   probes and matched timing comparisons are explicitly requested investigations.
6. When a validated repair adds new reusable knowledge, preserve its complete
   case and improve the applicable method here. Follow-ups update the same case; a new summary does not replace
   or delete its underlying evidence.

Current commands and final-check scope belong to
[development](DEVELOPMENT.md#local-verification-and-ci),
[caching](CACHING.md#shared-ci-protocol) and [the toolkit](../scripts/README.md).
Historical command sequences in records describe their original runs.

## Conversion boundaries

**Type the complete comparison.** Fix actual source/target objects, Hom carriers,
intermediate isomorphisms, input/output values and structures before applying a
generic law. For module sheaves, keep a single `M : X.Modules` and its actual
`M.presheaf.map` throughout. Type the lambda in `congrArg` and both endpoints
of a transport. An annotation that elaborates to the same core term may do
nothing; inspect which representation differs.
[Module-section case](performance/keep-one-representation-of-module-sections.md).

**Prove the whole relevant equation before evaluating components.** Compose,
transport or cancel the original transformations/isomorphisms over variables,
match the consumer's exact association and whiskering, then evaluate once.
When that still fails, parameterize the complete actual comparison `E`,
input `x`, output `y` and canonical equations so the generic conclusion is
already the consumer's literal `E x = y`. The supplied equations remain proved
from the original data; abstracting only one map or the final scalar step can
leave the costly specialization unchanged.
[Whole module exchange](performance/whole-module-exchange-comparisons-before-evaluating-components.md),
[site-cohomology factories](performance/site-cohomology-share-the-comparison-definition-not-only-its-proof.md).

**Transport dependent data early.** Fix degree equalities, finite-subtype ranges,
Over source objects, index families and equality orientation before forming
concrete dependent carriers. Keep the original arithmetic spelling when it
determines a transport. If two relative objects have differently presented
structural maps, use their proved comparison arrows and triangles instead of
forcing a carrier rebase.
[Explicit transports](performance/formal-line-bundle-algebraization-explicit-transports.md),
[tuple cochains](performance/original-tuple-cochains-normalize-typed-carriers-before-transport.md).

**Isolate witness selection when typed endpoints are insufficient.** For finite
product equivalences, prove preimage selection and inversion over plain
functions, the two actual equivalences and their component equation; then supply
the original Ext comparison and coefficient-naturality law. Retain finite-index
and Ext universes rather than adding a new premise.
[Finite Ext witness case](performance/étale-derived-comparisons-share-the-equation-then-specialize.md#finite-ext-tests-isolate-witness-selection).

**Use finite typed calculations for a specific rewrite failure.** Apply the
native map's theorem directly when it already fits, such as `Ideal.map_pow`
on the original `includeRight`. Compose exact laws with `congrArg`,
`congrArg₂` and `Eq.trans` when broad rewriting exposes the wrong carrier.
Stop extensionality at the intended element/transformation; qualify colliding
names such as `CategoryTheory.Functor.map_id` and `Limits.Pi.map`.

| Specific recorded failure | Targeted remedy |
| --- | --- |
| Permutation ordering in `simpa only [mul_comm]` | Compose `(mul_comm w z).trans hzw` directly. |
| Forward and reverse composition rules form a rewrite loop | Use a finite calculation through the original unit. |
| `p = C (p.coeff 0)` rewrites `p` inside its own right side | Use that equality once through congruence and composition. |

[Permutation case](performance/binary-form-section-and-geometric-point-typing.md),
[composition loop](performance/use-a-finite-original-unit-calculation-for-constant-direct-image-coordinates.md),
[self-reference](performance/picard-tangent-space-prove-additive-group-algebra-abstractly-then-specialize.md#avoid-self-referential-coefficient-simplification).
These are distinct failures; they do not justify banning `simp` or `rw`.

Choose the smallest complete boundary that keeps the original interface.
The [affine-refinement case](performance/affine-refinement-through-literal-mate-types.md)
instead benefited from removing a Type-valued constructor and keeping literal
component arrows. A simpler mathematical route also depends on its proved
preconditions: the [terminal-chart repair](performance/reindexed-direct-image-comparisons-evaluate-a-whole-identity-first.md#rebase-sections-to-the-terminal-coefficient-chart-before-equality-descent)
required the original fixed-base natural isomorphism and retained its
affine-stage/small-index scope and original section maps.

## Shared constructions and equations

**Use the same regular proposition on both sides.** State the exact original
equation through one regular definition, with actual objects and arrows as
arguments, in the generic producer, concrete statement and consumer. Examples
include `CompEq`, `GlobalSectionImagesEq`, `QuotientFinite` and
`ExactComparisonSquareEquation`. Wrapping only one side, or specializing
every intermediate calculation separately, can leave the expensive conversion.
The concrete equation still needs its original proof.
[Equation/field cases](performance/equation-proofs-presentations-and-structure-fields.md),
[conormal comparisons](performance/preserve-regular-equations-through-conormal-comparisons.md).

**Share the actual constructor, not only a theorem about rebuilt data.** Reuse
the same function/functor/comparison head in definitions, statements and
applications. If needed, construct the complete comparison inside the generic
producer. A tensor-chart witness had to construct its tensor comparison
internally; coefficient-single tests had to reach the actual `zmodSingle`
head expected by their provider.
[Tensor witness](performance/construct-the-tensor-comparison-inside-the-shared-chart-witness.md),
[coefficient-single cases](performance/share-the-actual-coefficient-single-data-head-before-transporting-exchange-tests.md).

**Name repeated equation proofs before elaborating statement and body.** Use
the same named degree/transport lemma with atomic arguments inside
`eqToHom`, `pullbackCongr` and `mapComp'`. Proof irrelevance still requires
compatible proof types; the particular delta/proof-type explanation remains
conditional where the record did not establish the conversion pair.

**Keep values and their equations together when they must agree literally.**
Project the same arrow/value-and-equation witness instead of rebuilding each
part. Move complete supplier-to-witness conversion to the abstract producer
when the concrete consumer still pays for it. Packaging alone is insufficient:
Motivic's context variants regressed its recorded constructor cost, and the
retained 141-second observation does not improve the original 135-second one.
[Complete original Motivic observations](https://github.com/kangxyz/motivic/blob/main/docs/performance/observed-module-costs.md).

**Preserve the consumer's reduction interface.** A local constructor may retain
component formulas by beta/zeta reduction; an independently applied helper can
introduce new instance-proof conversions. Expose the equations the actual API
needs. Abstract theorem parameters do not require replacing canonical data by
Lean `opaque` or changing global transparency.
[Tensor/Span and rejected helpers](performance/what-the-measurements-establish.md).

**Bridge an isomorphism definition and its value before projecting.** At an
identified boundary, prove a named `rfl` value equation at variable arguments,
transport it with `congrArg`, then compose with the existing lemma. The
Hilbert-scheme case compared at `Iso` level before applying `.hom`; plain
application and tensor-spelling alignment had not solved it. Its proposed
projection/delta cause remains a candidate.
[Original value-bridge case](performance/hilbert-scheme-direct-images-compare-isomorphism-values-at-the-iso-level.md).

## Instances and universes

**Supply an already proved dictionary at its exact type.** Bind repeated
universal instances locally, pass existing finite-index witnesses directly,
use `inferInstanceAs` for the actual `HasExt`, and obtain preservation from
the original equivalence/adjunction before projecting its field. Use
`IsIso.mono_of_iso` when that is precisely the available hypothesis.
[Preservation dictionary](performance/pass-the-preservation-dictionary-of-an-equivalence-explicitly.md).
These restrict known search; they do not replace missing mathematics with
assumptions or global priority changes.

**Fix the category/structure before dependent universe synthesis.** In the
small-model/sheafification case, `smallCategorySmallModel : SmallCategory.{max u v}`
was bound before dependent sheafification/Grothendieck synthesis. The separate
ModuleCat Kan-preservation case selected exact shape-indexed instances.
Keep independent Ext, site, scheme and derived-category universes; resolve
underconstrained expressions without imposing artificial universe equalities.
[Small-model case](performance/site-cohomology-share-the-comparison-definition-not-only-its-proof.md),
[Kan-preservation case](performance/pinning-the-actual-module-universe-in-a-kan-extension-preservation-proof.md).

**Retain native parent structures and scalar actions.** Use the original
localization ring, module action, grading and comparison map. Reprojecting a
`CommRing`, choosing another Ore structure or synthesizing another grading
can create an incompatible boundary. Matching underlying functors also does
not identify their supplied `CommShift` coherence; a missing provider import
still needs that provider.
[Localization](performance/retain-native-localization-structures.md),
[grading](performance/retain-the-given-grading-in-an-exceptional-chart-quotient.md),
[shift structures](performance/keep-native-shift-structures-explicit-in-the-canonical-exchange-proof.md).

**Reach residue fields by instantiating variable-field statements.** State
finiteness and dimension facts for a variable field `K` and data over
`Spec (CommRingCat.of K)`, then instantiate them at `κ(t)`. Re-deriving such a
fact at the residue field cost 68 s of kernel checking in one declaration;
after instantiation the consumer leaf built in 10 s. The variable-field
lemmas keep their own cost.
[Field-point case](performance/field-point-cohomology-dimensions-specialize-residue-fields-through-variable-field-statements.md).

**Request only the structure used.** Prefer `Ext.precompIsoAddEquiv` for an
additive argument, native sized `Subobject.sInf` when no complete lattice is
needed, and an available native isomorphism/field-point API. The original
mathematical conditions govern that choice.
[Additive Ext](performance/additive-ext-transport-avoid-an-irrelevant-integer-module-diamond.md),
[sized infima](performance/transport-section-equivalences-before-specializing-the-qc-pseudofunctor.md#use-native-sized-subobject-infima-instead-of-rebuilding-a-concrete-lattice).

## Build-and-check costs

- Keep compatible native artifacts and successful check categories. A cache
  candidate is not current lint/axiom evidence; a successful unchanged frontend
  in a failed graph retains only its actual scope.
- Use focused dependency owners for independent interfaces. Batch necessary
  edits to widely imported providers, and preserve unaffected consumers.
- When target graphs are already concurrent, avoid compiling the same unresolved
  prerequisite in both: keep it with one owner and partition the remaining
  pending branches. This does not require parallel workers or a new scheduler.
- Check the actual in-package consumer when an interface change can move cost.
  The rejected Scalars.Open factory transferred its saving to its caller;
  producer savings alone do not establish a whole-library improvement.
- Reuse matching checker setup through the existing native entry. A missing tool
  needs that dependency, not a clean mathematical rebuild. Distinguish a driver
  launch failure from a reported source-style error.
- Distinguish frontend caps/threads, job concurrency, aggregate RSS/cgroup memory
  and runner reserve. Inspect a resource failure before changing mathematical
  proofs in response to secondary type errors. A serialized tail cannot use all
  compiler slots, and historical calibrations do not prescribe a universal profile.
- Resolve actual cache/input-observer failures before continuing checks. Current
  content rechecking handles ctime-only link activity; an old reflink workaround
  is not routine preparation.
- Use exact import casing, distinct local-instance declaration names and the
  exposure boundary the public implementation actually needs. An import failure
  or unavailable private helper is different from expensive proof conversion.

[Pending-dependency overlap](performance/late-lint-repairs-and-dependency-invalidation.md),
[cost transfer](performance/whole-library-pass.md),
[resource observations](performance/remote-resource-calibration-on-the-unchanged-library.md),
[checker memory](performance/declaration-lint-memory-in-ci.md),
[local instance names](performance/local-instance-names-must-remain-distinct-across-actual-imports.md).
Current operating guides own commands; historical split-linter, client, replay
and control sequences in those records do not become present procedures.

## Requested diagnosis and evidence

For an explicitly requested investigation:

1. Keep one implicated declaration/module on its actual pinned source, prepared
   dependencies and effective options. Put diagnostic outputs in scratch.
2. Separate imports, elaboration, synthesis, tactics, kernel work, lint and
   serialization. Instrumentation can itself cause failure.
3. Inspect selected profiler frames, compact expression heads and actual implicit
   arguments. Unfolding counts are not per-constant time; large printed terms
   can consume diagnostic resources.
4. Distinguish forming a proposition from checking a value/proof. A faithful
   type probe puts `P` in a theorem binder
   (`theorem probe (_h : P) : True := True.intro`);
   `def probe : Prop := P` can measure a different nested-proof construction.
5. Compare only the scope requested. For a speedup claim, use matched unprofiled
   conditions: relevant source/dependencies, threads, flags, outputs, cache
   treatment and measurement mode, including consumers when work can move.

[Original diagnostic records](performance/a-focused-diagnostic-procedure.md),
[formation/value distinction](performance/values-at-concrete-fibre-products-over-spec-commringcatof-a.md).

A repaired-module pass does not supply a successful speedup baseline, consumer
pass or compiler-cause attribution. Keep profiled, unmatched and retained author
observations distinct; cached modules have no new timing. Inclusive profile
weights and parallel job durations cannot be summed into wall time. Missing old
logs remain missing; relocating a record does not revalidate it.

### Search upstream references

If existing cases do not cover the failure, search Lean, Mathlib and the affected
library's issues, PRs, discussions and official documentation by actual diagnostic,
public symbol, phase and version. Read the reproduction and proposed code, then
check the pinned implementation/release. Similar wording or a merged PR is a lead.

Existing leads such as `simp -implicitDefEqProofs`, `as_aux_lemma`,
data/proof separation and regular definition boundaries apply to particular
problems. Their [original sources and limitations](performance/methods-and-evidence.md)
must be matched to the current task; old issue states are historical.

## Preserve methods and full cases

Keep actionable methods and this decision process in `PERFORMANCE.md`.
When a validated repair adds new reusable knowledge, add a complete case or
update its existing record under `docs/performance/`, retaining
conditions, failed attempts, measurements, source identities and evidence limits;
update the same case for follow-ups and its [index](performance/README.md).
Another run/pass or unchanged application of a known method needs no new entry.
That concerns new writing; all existing case records remain complete.
Refining either layer must preserve the other. Summaries and Git-history links
do not replace case text, and an index alone does not replace the methods here.
Documenting experience adds no build, benchmark or acceptance cycle; mathematical
trust and independent mathematical/writing review retain their existing owners.
