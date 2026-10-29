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
| A compilation bottleneck or unclear cause | [Diagnosis and evidence](#diagnosis-and-evidence) |

## Repair workflow

Use these decisions within ordinary proof iteration:

1. Locate the failing phase from existing feedback: cache/input preparation,
   imports, elaboration/instance search, tactic work, kernel checking, checker
   startup or serialization. A short proof or completed tactic can still leave
   expensive kernel conversion. If feedback cannot locate an actual bottleneck,
   use [targeted diagnosis](#diagnosis-and-evidence) to guide the next repair.
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
   [upstream reference search](#search-upstream-references).
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
For a functor whose values are literal fibre products, such as `familyScheme p`, name its maps
with the literal source and target and state every lemma through that name; conversions between
`(familyScheme p).map t`-typed maps and modules over `pullback p T.hom` cost 44–86 s of type
checking each. [Family-map case](performance/linear-system-family-maps-type-them-between-the-literal-fibre-products.md).
Type an `Over.isoMk` between objects whose structure maps agree only up to a proof at the actual
object (`Iso.refl (Spec (.of k))`), not at the `left` of either `Over` object: the latter cost
89 + 44 s of kernel checking for one definition, the former under 1 s. Compare kernels of a concrete
presheaf only through generic equivalences such as `AddEquiv.addSubgroupCongr`; `rfl` between two
subtypes of `Pic_{X/k,(fppf)}` exhausted kernel memory.
[Over-category comparison case](performance/over-category-comparisons-type-identity-isomorphisms-at-the-actual-object.md).

For continuity coefficient and cohomology legs, type the original component
inverse or input at the literal diagram object, then compose its whole value
law or apply native `H.map_comp_apply` directly. Reuse one typed alias for the
original inverse constant-source arrow across assemblers; supply the given
`HasExt` at its projected apex type. Retain the original maps and premises.
[Continuity typed original endpoints](performance/continuity-typed-original-endpoints.md).

**Prove the whole relevant equation before evaluating components.** Compose,
transport or cancel the original transformations/isomorphisms over variables,
match the consumer's exact association and whiskering, then evaluate once.
When that still fails, parameterize the complete actual comparison `E`,
input `x`, output `y` and canonical equations so the generic conclusion is
already the consumer's literal `E x = y`. The supplied equations remain proved
from the original data; abstracting only one map or the final scalar step can
leave the costly specialization unchanged.
For native square and triangle comparisons, first derive the whole law on the
actual original isos, using independently proved identities to the same
coherent data. Then evaluate with raw variable-category lemmas at those same
heads. Share the original coefficient constructor and instantiate its actual
functors, units and adjunctions once; same-endpoint isos alone do not preserve
the map. [Whole original comparison laws](performance/whole-original-comparison-laws.md).
[Whole module exchange](performance/whole-module-exchange-comparisons-before-evaluating-components.md),
[site-cohomology factories](performance/site-cohomology-share-the-comparison-definition-not-only-its-proof.md).
For a sheafified tensor associator, prove typed three-isomorphism cancellation
and a variable-functor naturality/map-square equation before supplying the
actual `L.obj` and tensor endpoints.
[Chosen-associator case](performance/abstract-foundation-construction-boundaries.md#prove-the-chosen-associators-typed-square-before-tensor-specialization).

**Consume a producer equation at its actual inferred type.** If the original
proof application checks at its inferred proposition but conversion to a
manually restated native equation times out, retain it with unannotated
`have hcube := producer ...`. Feed that equation directly to complete
variable-category morphism cancellation, keeping the original functor, target
arrow and four comparison edges explicit while the equation infers its middle
component and endpoints. Prove every native invertibility and conservativity
fact; keep the original arrow in the conclusion. Generic whole-cube cancellation
alone and explicit native functor/projection typing did not close this case.
Raw dictionary differences and type-size measurements locate a diagnostic
boundary, not a unique kernel cause. The full frozen theorem and later generic
production module passed; the thin production consumer remains pending in this
record. [Inferred native equation case](performance/inferred-native-comparison-equations.md).
The later [source-bound integration milestone](performance/inferred-native-comparison-equations.md#integration-milestone-2026-10-27-source-33013d99)
records the thin consumer passing on source `33013d99`; later changed imports
and downstream endpoints retain their own coverage limits.

**Infer a composed equality before normalizing it against a concrete goal.**
When `simpa ... using` hits recursion limits or a type mismatch, compose the
already proved equations without an expected target (`have hfinal := hmap.trans
hclass`). Normalize that inferred hypothesis and the actual goal in their
respective locations, then use `exact hfinal`. The Field case passed in two
faithful isolated candidates and the exact adopted production module; it added
no helper, model, import, option or hypothesis. Identical printed expressions do
not identify the hidden conversion cause, and module times are not proof-only
or matched speedup evidence.
[Field follow-up](performance/inferred-native-comparison-equations.md#field-follow-up-infer-the-composed-equality-before-normalization).

**Transpose the whole original composite over a variable adjunction.** When
native sheafification zero/naturality laws elaborate but their final concrete
transport still times out, use a helper whose conclusion is the actual supplied
`k ≫ g = 0`. Keep the same adjunction and arrows, pass the whole equation
`(adj.homEquiv P A) k = i` and proved presheaf composite, and pin naturality's
source/target objects before specialization. At the caller, discharge those
equations from the original unit law and ring calculation; do not add them as
public assumptions or return a rebuilt inverse-HomEquiv map for another concrete
comparison. A faithful formation check and prefix markers distinguish this
frontier from earlier work; aggregate unfolding counters do not identify the
exact conversion pair.
[Native Artin–Schreier case](performance/native-artin-schreier-whole-transposition.md).

**Match the actual transfer before cancellation.** If a cancellation lemma
accepts one presentation of a cohomology transfer while its native consumer
supplies another, first prove the original transfer's whole value formula
over variable schemes and its actual model data. Supply literal chart,
coefficient and transport values at the completed cancellation boundary.
Retain independently supplied Ext worlds and derived models.
[PBC transfer boundary](performance/pbc-original-map-and-finite-model-boundaries.md#match-the-actual-cohomology-transfer-before-eight-model-cancellation).

**Evaluate concrete composition over variable objects.** After proving the
whole equation of the actual raw group maps, apply `congr_hom` and simplify
composition in a helper over variable `AddCommGrpCat` objects. Have the native
consumer supply those raw maps and their whole equation once. Native evaluation
followed by simplification can leave carrier/functor presentations that print
identically but are still expensive to compare. Preserve the original concrete
category instances and cohomology worlds.
[Original raw rectangle case](performance/pbc-original-map-and-finite-model-boundaries.md#evaluate-the-raw-group-rectangle-before-specializing-cohomology-objects).

**Retain the indexed whole germ law before choosing a point.** Prove the
original additive-map equation at variable `d` in the actual category of
elements. Specialize that whole equation to `{obj := U, val := p}`, then
evaluate it in a helper over variable group objects. Abstracting only the
scalar law or dropping the derived-model context need not remove the indexed
specialization. Preserve the original stalk and cohomology worlds.
[PBC indexed-germ completion](performance/pbc-original-map-and-finite-model-boundaries.md#retain-the-whole-indexed-germ-law-before-point-evaluation).

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

**Check whether the consumer needs another implementation.** Follow the
[minimal-choice rule](INTERFACES.md#minimal-implementation-choices): use one
chosen realization per mathematical category, and prefer Ext, natural-degree
right-derived functors or ordinary invariant tests when they suffice. Put a
necessary comparison or choice-independence proof at its actual boundary.
The restored PBC consumer retained its public four-output conclusion through
ordinary exchange and zero-object tests; its optional reference-model cube
was held, with failed diagnostics preserved.
[Route-retirement case](performance/abstract-foundation-construction-boundaries.md#retire-optional-implementation-transport-at-the-actual-consumer).

**Use the same regular proposition on both sides.** State the exact original
equation through one regular definition, with actual objects and arrows as
arguments, in the generic producer, concrete statement and consumer. Examples
include `CompEq`, `GlobalSectionImagesEq`, `QuotientFinite` and
`ExactComparisonSquareEquation`. Wrapping only one side, or specializing
every intermediate calculation separately, can leave the expensive conversion.
The concrete equation still needs its original proof.
[Equation/field cases](performance/equation-proofs-presentations-and-structure-fields.md),
[conormal comparisons](performance/preserve-regular-equations-through-conormal-comparisons.md).

For native raw-Hom charts, retain the same regular composition equation in
its actual overlap relation and the generic cancellation helper. Prove the
original diagonal scalar, transition identity and fully typed identity
restriction separately, then compose those equations with the existing
restriction-map view. This avoids asking one concrete simplification to
traverse the entire pseudofunctor implementation. A regular equation used by
a public definition must have the required public visibility; a private proof
helper can remain private.
[Raw-chart case](performance/native-line-bundle-raw-chart-equations.md).

**Align a complete shared construction with its original proof inputs.** Build
the full operational family once before its concrete representation. When
the original equation still meets expensive conversion, normalize object and
constructor projections in the instantiated core telescope and original
component proof types before supplying the actual maps and proofs. Preserve
the economical raw equation, actual values and selected realization. The
[Global follow-up](performance/inferred-native-comparison-equations.md#global-follow-up-shared-construction-and-normalized-proof-inputs)
records the failed diagnostics and the source-bound production module pass.

**Keep equality proof inputs through projection normalization.** Build the
whole law from the original comparison data and apply its raw evaluator only
after identifying those same values. Normalize needed definitional projections
in the instantiated telescope and proof-input types; if `simp` replaces an
original equality type by `True`, use the appropriate definitional-only
normalization and supply the original equality. The
[continuity triangle case](performance/inferred-native-comparison-equations.md#continuity-triangle-follow-up-preserve-original-proof-inputs)
records the failed input applications and source-bound native module pass.

**Share the actual constructor, not only a theorem about rebuilt data.** Reuse
the same function/functor/comparison head in definitions, statements and
applications. If needed, construct the complete comparison inside the generic
producer. A tensor-chart witness had to construct its tensor comparison
internally; coefficient-single tests had to reach the actual `zmodSingle`
head expected by their provider.
[Tensor witness](performance/construct-the-tensor-comparison-inside-the-shared-chart-witness.md),
[coefficient-single cases](performance/share-the-actual-coefficient-single-data-head-before-transporting-exchange-tests.md). A later injective-assembly repair adds a lower view at variable
`Z`, with the original construction equation `Z = U ⋙ single`, then supplies
the actual `zmodSingle` and `rfl` at the native call. The full assembly and
original data remain intact. [Proper injective follow-up](performance/inferred-native-comparison-equations.md#proper-injective-follow-up-retain-the-original-single-head).
For localization triangles, share the actual lift, whole vertex factorization
and specified first/second arrows with the transported original connecting
arrow; retain named original-value equations for existing unfolding consumers.
[Triangle and original-value case](performance/abstract-foundation-construction-boundaries.md#keep-intrinsic-comparisons-whole-and-retain-original-value-views).
For a slice comparison built from an equivalence, share the native
`compInverseIso` constructor and a regular whole counit equation over variable
categories, then specialize those same heads. At its product boundary, an
explicit equivalence retaining the original section values can relate the
actual fibre to the existing chosen product fibre.
[Validated slice case](performance/etale-slice-shared-comparison.md).

**Reconcile native composition branches once.** For a derived comparison built
from two composition isomorphisms and an ordinary isomorphism, use the installed
canonical composition maps in one shared constructor. Prove their whole unit
equations and identify the existing homology, injective, acyclic-image and
selected-derivability branches by unit uniqueness. The geometric callers can
then share both the construction and its unit law without identifying their
chosen derived models. Preserve named original-factor value laws for consumers
that previously unfolded the concrete definition.
[Derived three-factor pilot](performance/right-derived-three-factor-comparisons.md).

**Preserve an original map's literal constructor when its formula is the API.**
For a zero-power ideal comparison, prove invertibility of the original inclusion
and use `asIso` on it, so the forward-map equation is `rfl`. At a different
boundary, move the complete coefficient calculation, elementary typed linear
argument or localization-and-kernel producer over variables before specializing;
coordinate helpers alone may leave the concrete conversion unchanged.
[Surface-resolution cases and evidence](performance/surface-resolution-constructor-boundaries.md).

**Paste whole section and coefficient families through the same constructor.**
Construct the actual comparison from its original section transformation and
coefficient transformation. Prove its whole composition, transport and
`CommSq` laws while the functors remain variable. Feed the existing relative
`TwoSquare` pasting equality and whole unit square to this constructor before
choosing a coefficient. Keep native value formulas as views of that same
construction; a scalar wrapper around rebuilt data can leave the original
specialization unchanged.
[PBC whole-family completion](performance/pbc-original-map-and-finite-model-boundaries.md#paste-whole-section-and-coefficient-comparisons).

**Keep the coefficient family variable at a component boundary.** When a native
component application still compares a composite functor object with nested
object applications, construct the original evaluation and component inside a
producer over the coefficient functors and the whole transformation. Supply
its original whole invertibility proof, then specialize. A scalar map-and-laws
witness and fixed scheme endpoints alone did not close the recorded native
initializer; the family construction did. Its then-failing CH and section-square
consumers have later [completion records](performance/pbc-original-map-and-finite-model-boundaries.md#complete-the-original-pbc-section-germ-and-stalk-consumers).
[Chart exchange family](performance/pbc-original-map-and-finite-model-boundaries.md#construct-the-chart-exchange-from-its-whole-coefficient-family).

**Transport original whole values before projecting a primitive law.** When a
supplied scalar law stores a definitionally equal scheme endpoint or model
alias differently, extract the actual whole transformations and retain their
original data. Prove their value equality before taking a coefficient component.
Pass both values and this proved equality to the variable-functor consumer;
project and apply Gamma there, then use the primitive law. A native component
transport can leave the same conversion boundary. Keep separately typed model
arguments and omit unused section instances rather than assuming a generated
helper's universe order.
[Chart whole-value transport](performance/pbc-original-map-and-finite-model-boundaries.md#transport-the-actual-chart-exchange-value-before-projecting-its-scalar-law).

**Return the native quantified property whole.** At a scalar-to-property
boundary, have the factory return the same regular quantified predicate as its
consumer, and fix any phantom model arguments explicitly inside that factory.
A scalar `IsIso` producer, even with the complete actual map as an argument,
can leave the concrete native-property specialization expensive.
[Bounded target-locality case](performance/pbc-original-map-and-finite-model-boundaries.md#return-the-whole-standard-bounded-target-test).

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

**Preserve a compiled fixed-law witness when the failure is simplification order.**
At the recorded boundary, the generated constructor-injectivity rule becomes
redundant only after contextual fixed-map equalities normalize its arguments.
Register that existing rule with `[simp↓]` so it runs before those arguments
are simplified. Keep the exact structure, constructor, provider and projections
when replacement representations disturb their native conversion. Local simp
erasure did not remove the exported registration in this case. This is a
bounded repair for the inspected rule, not a scheduling convention for all
constructor lemmas.
[PBC constructor-rule order](performance/pbc-original-map-and-finite-model-boundaries.md#simplify-the-retained-constructor-rule-before-its-arguments).

**Preserve the consumer's reduction interface.** A local constructor may retain
component formulas by beta/zeta reduction; an independently applied helper can
introduce new instance-proof conversions. Expose the equations the actual API
needs. Abstract theorem parameters do not require replacing canonical data by
Lean `opaque` or changing global transparency.
[Tensor/Span and rejected helpers](performance/what-the-measurements-establish.md).
When the proof needs only the defining equation of a large constructed value,
such as a lift through an open immersion, introduce it with
`obtain ⟨x, hx⟩ : ∃ x, … := ⟨…, …⟩` rather than `let`; in one combined repair
this, with the per-component step split into lemmas, removed a 341-second `whnf`
timeout in `refine`, and the attribution to `let` is a candidate.
[Open-immersion lift case](performance/open-immersion-lifts-in-long-proofs-keep-only-the-defining-equation.md).

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
At native Scheme/module wrappers, a functor ascription alone may leave the
preservation predicate at another category/zero head. Supply the existing
generic proof at the caller's explicit category and structure arguments.
[Native evaluation and zero dictionaries](performance/native-evaluation-zero-dictionaries.md).
For projected geometric fibres and cone apices, bind the original `HasExt.{e}`
at the exact `Over`-left or `.pt.left` type with `inferInstanceAs`.
[PBC projected dictionaries](performance/pbc-original-map-and-finite-model-boundaries.md#retain-the-whole-indexed-germ-law-before-point-evaluation).
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

**Specify residual universes hidden by `max`.** A common output carrier does
not uniquely determine each input universe. Pass those residual parameters
explicitly through constructor, helper and corollary calls; retain the actual
scalar parent and whole extensionality carrier, and give native fully faithful
Hom equivalences their actual `X` and `Y`. Endpoint annotations alone need not
resolve all those inputs.
[Generic tensor–Hom and pullback case](performance/abstract-foundation-construction-boundaries.md#pin-residual-universes-through-noninjective-maxima).

**Retain native parent structures and scalar actions.** Use the original
localization ring, module action, grading and comparison map. Reprojecting a
`CommRing`, choosing another Ore structure or synthesizing another grading
can create an incompatible boundary. Matching underlying functors also does
not identify their supplied `CommShift` coherence; a missing provider import
still needs that provider.
[Localization](performance/retain-native-localization-structures.md),
[grading](performance/retain-the-given-grading-in-an-exceptional-chart-quotient.md),
[shift structures](performance/keep-native-shift-structures-explicit-in-the-canonical-exchange-proof.md).
In generic ringed-site adapters, retain the exact forgotten `RingCat` sheaf and
scalar/tensor head, and check the native `Opens` Hom universe. If component
`IsIso` synthesis misses that literal head, take a component of the actual
whole counit NatIso and pass its proved dictionary explicitly.
[Native parents and counit case](performance/abstract-foundation-construction-boundaries.md#take-the-whole-counit-isomorphism-then-supply-its-literal-dictionary).

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
- Separate primitive coefficient aliases from classification-heavy providers.
  Preserve literal names, types, RHS and native lifts, reexport the leaf from
  the geometric owner, and redirect only coefficient consumers. Bind existing
  base instances at the actual functor image when needed. Retain matching
  incremental passes; import-edge removal alone is no timing claim.
  [Constant coefficient import boundary](performance/constant-coefficient-import-boundary.md).
- When target graphs are already concurrent, avoid compiling the same unresolved
  prerequisite in both: keep it with one owner and partition the remaining
  pending branches. This does not require parallel workers or a new scheduler.
- Check the actual in-package consumer when an interface change can move cost.
  The rejected Scalars.Open factory transferred its saving to its caller;
  producer savings alone do not establish a whole-library improvement.
- Reuse matching checker setup through the existing native entry. A missing tool
  needs that dependency, not a clean mathematical rebuild. Distinguish a driver
  launch failure from a reported source-style error.
- Inspect the pinned native checker's import loop before passing overlapping
  module arguments. If each imports the same package environment, establish
  with the native source parser that one terminal target reaches every required
  root and origin, then select it once. Retain its registered text/deferred and
  any environment checks, separate declaration predicates and axiom-audit
  roots. Metadata-cache reuse and fewer jobs alone did not resolve the recorded
  repeated-environment pressure.
  [PBC terminal-check recovery](performance/pbc-original-map-and-finite-model-boundaries.md#run-the-native-builtin-check-on-one-complete-terminal-environment).
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

## Diagnosis and evidence

At a compilation bottleneck, actively use targeted compiler diagnostics, scoped
traces, profiling or scratch probes when existing feedback does not locate the
cause or guide the next repair. Normal troubleshooting and targeted compilation
diagnostics need no separate user approval and add no routine benchmark or
acceptance stage. Kernel replay and separate client checks remain excluded from
ordinary work; mathematical trust and independent mathematical/writing review
retain their existing requirements.

1. Keep one implicated declaration/module on its actual pinned source, prepared
   dependencies and effective options. Put diagnostic outputs in scratch.
2. Separate imports, elaboration, synthesis, tactics, kernel work, lint and
   serialization. Instrumentation can itself cause failure. For a native-faithful
   scratch probe, obtain `lake --no-build setup-file actualModule` and pass the
   resulting `--setup`, retaining exact module name, `isModule`, imports and all
   library options. A managed resource wrapper alone does not forward them;
   [A's earlier option-equivalence interpretation was withdrawn](performance/inferred-native-comparison-equations.md#native-option-faithfulness-and-withdrawn-interpretation).
3. Inspect selected profiler frames, compact expression heads and actual implicit
   arguments. Unfolding counts are not per-constant time; large printed terms
   can consume diagnostic resources.
4. Distinguish forming a proposition from checking a value/proof. A faithful
   type probe puts `P` in a theorem binder
   (`theorem probe (_h : P) : True := True.intro`);
   `def probe : Prop := P` can measure a different nested-proof construction.
5. Compare only the scope needed for the investigation. For a speedup claim,
   use matched unprofiled conditions: relevant source/dependencies, threads,
   flags, outputs, cache
   treatment and measurement mode, including consumers when work can move.

[Original diagnostic records](performance/a-focused-diagnostic-procedure.md),
[formation/value distinction](performance/values-at-concrete-fibre-products-over-spec-commringcatof-a.md).

A repaired-module pass does not supply a successful speedup baseline, consumer
pass or compiler-cause attribution. Keep profiled, unmatched and retained author
observations distinct; cached modules have no new timing. Inclusive profile
weights and parallel job durations cannot be summed into wall time. Missing old
logs remain missing; relocating a record does not revalidate it. A large `refine`
or closing `linting` entry right after heavy definitions may be waiting for the
asynchronous kernel checks of the preceding declarations (a candidate reading
whose totals matched in two profiles); compare it with those checks before
attributing it to the tactic
([profile reading](performance/over-category-comparisons-type-identity-isomorphisms-at-the-actual-object.md)).

**Keep a diagnostic frontier distinct from a repair result.** When short
cohomology adapters have large named Kernel intervals, inspect one actual
site/Ext/additive presentation and its scalar consumer before changing result
types or transparency throughout the API. Elaboration traces through
`Ext.homEquiv`, `Localization.SmallHom.equiv` or `equivShrink` identify a
candidate boundary, not the exact kernel reduction pair or a speedup. Repeated
zero-preservation synthesis at literal category/zero heads can justify a local
pilot with an existing witness. Retain source/setup provenance, structured
frames and exact excerpts; keep an oversized authoritative raw trace at its
hash-bound durable locator. Do not allocate unprofiled wall time from overlapping
instrumented intervals. [Čech diagnostic frontier](performance/cech-intrinsic-conversion-frontier.md).

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
