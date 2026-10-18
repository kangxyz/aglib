# Migration work and validation boundaries

## Current source and open boundaries

The documentation audit uses source revision
`c8ef63f1f0ad26c8bca83f2bf2a8559fffdc356e`. The family guides and
[INTERFACES.md](INTERFACES.md) describe the implemented mathematics; the
checkpoints below retain their original source and validation bases. A source
inventory, documentation correction or historical successful run does not
establish fresh whole-library or downstream acceptance.

| Area | Implemented source | Remaining boundary |
| --- | --- | --- |
| Base change | Canonical affine module mate; qcqs flat base change for original cohomology, D+ coefficients with QC homology and native higher direct images | General nonflat sheaf-valued comparison; the full arbitrary-base `LocalFreeCohomologyBaseChange` input family |
| Proper cohomology | Noetherian proper finiteness; coherent higher direct images over locally Noetherian targets; universal finite-projective models for coherent relatively flat coefficients over Noetherian affine bases | Direct images of arbitrary perfect coefficients |
| Differentials and duality | Relative differential sheaf and fixed smooth rank over arbitrary bases; field-linear projective-space Serre duality and the original projective-space derived Serre comparison over Noetherian rings | Global Euler-sequence gluing, canonical-bundle identification, general smooth-projective and proper duality |
| Downstream adoption | The [downstream guide](DOWNSTREAM.md) distinguishes inspected dependency pins from historical migration and validation records | Reconcile actual dependency checkouts and check affected consumers before claiming downstream acceptance |

The [cohomology plan](COHOMOLOGY_PLAN.md) gives the exact source suppliers and
remaining dependencies. Migration JSON files are records of identified source
cuts and checks, not a complete live inventory of this revision. Original
hashes and execution records remain fixed when later source changes.

## Documentation correspondence audit, 2026-10-18

The audit reviewed all 293 Markdown documents and 20 documentation JSON files
at the source revision above, comparing the family guides with current Lean
declarations, section hypotheses and source docstrings. Corrections distinguish
proved suppliers from remaining inputs, retain missing mathematical hypotheses,
repair source/import routes and separate historical acceptance from present
interfaces. Original source, receipt and checker hashes and recorded numerical
evidence remain unchanged in the repaired migration records.

All 1943 local Markdown links and heading anchors resolve; fenced examples are
balanced and explicit Aglib imports name existing modules. All 20 JSON records
parse, and the repaired current-destination routes reach their actual source
owners. These are source/link checks; no executable Lean example was changed.

Source checks pass for generated enrollment, layout, source policy and
placeholders: 1159 production modules and 23 positive test modules. The 53
edited Lean files have identical noncomment tokens, including string literals;
only their documentation changed. No definitions, proofs, imports, dependency
pins or execution tooling were changed. This is documentation/source
correspondence evidence, not a fresh mathematical proof review, compilation,
whole-library replay or downstream acceptance.

## Heartbeat and compilation-performance checkpoint

The performance batch starts from `55b439b7219f12ad6ff2645b32d9f8b073dd8b28`.
Source policy now rejects every zero heartbeat budget, including documented
declaration-local overrides. Positive overrides remain documented and local;
the package default remains 200000. Four former allowances return to that
default in Cartesian restriction, the structure-module local-freeness proof
and the restricted-pushforward and finite-support component formulas.

Typed helpers and local constructors reduce concrete conversion in Godement
Tensor/Span, scalar degree-zero comparison and Mayer–Vietoris comparison.
Public statements, original module structures and canonical component formulas
are retained. Direct frontend invocation now propagates the selected native
thread and heap bounds. [PERFORMANCE.md](PERFORMANCE.md) records controlled
measurements, a rejected cost-transfer experiment and their limits.

All changed Lean leaves pass source compilation. Focused producer/consumer
builds and literal component checks pass for Tensor/Span, module-sheaf and
scalar changes. Cartesian also passes ordinary source compilation under the
CI heap/RSS profile where the original fails. The pre-merge source-only suite
passes 108 script tests and checks the 1112-module production source basis;
the separate native-cache
transport suite passes ten tests. The earlier cache-restoring aggregate pass
covers 1136 production/positive modules on its recorded earlier source basis.
Those earlier results cover their recorded source basis; the subsequent full
native CI checkpoint is recorded below. The two additional independent local
kernel replays remain outside that CI route.

The published first performance checkpoint is `197ca072`, merging the newer
general-source commits through `3da7bb3`. Its source-only suite checks 1159
production modules and passes the same 108 script tests. Fresh CI4 source
checks also pass OpenBaseChange and the retained Span; their bounds and a
rejected proof-helper trial are recorded in PERFORMANCE.md. Its actual CI
completes the 5024-job production/positive-test build and `lake test`, then
fails declaration lint with 91 diagnostics across 51 files. Later style,
axiom, controls, inventory and independent downstream stages are not reached.

The subsequent Restriction.Open and Map.Open constructors preserve their
literal component interfaces and pass the actual inverse, tensor, gluing and
localization consumers. The Map comparison includes measured downstream cost
transfer, recorded alongside its scoped net saving in PERFORMANCE.md. The
finite-support formula also passes its actual Exact.Euler consumer at the
default budget, with the recorded small RSS increase.

The subsequent performance checkpoint records a successful complete local native
`bash scripts/check.sh --rehash --ci` route: 1159 production modules, 23 trust-test
modules, 108 script tests, production/positive builds, declaration/style lint,
axiom audits, negative controls, exact compiled inventory and the independent
downstream build and audit. It uses the existing CI heap/RSS limits and current
native caches. Bounded kernel certificates retain the original public
propositions, transparent legacy aliases and actual data providers; the private
canonical simp forms also pass the pinned checker. The shared derived
pushforward shift instance keeps its literal original data. The additional
independent local kernel replays are not claimed by this CI checkpoint.

The remaining local heartbeat allowances are 800000 in the Cech
tensor-comparison component and 300000 in geometric restriction; neither
allowance is a runtime ranking.

## Cohomology integration checkpoint

The cohomology checkpoint `fae98131ae2f4cf4390e73f435dd1a62bcc5467f`
is integrated with the general-source checkpoint
`40af743ab794d607f566cec0c5417d8e4d02a735`.
The mathematical development and its remaining dependencies are recorded in
[COHOMOLOGY_PLAN.md](COHOMOLOGY_PLAN.md).

The new proofs supply canonical affine module base change, flat base change
for arbitrary quasicoherent coefficients and bounded-below complexes with
quasicoherent cohomology, and the original higher-direct-image comparison over
general bases. Proper coherent cohomology is finite over a Noetherian affine
base; affine localization gives coherence of higher direct images over every
locally Noetherian target. For coherent relatively flat coefficients, the same
bounded finite-projective Cech model computes all ordinary base changes over a
Noetherian base. Pointwise criteria, upper semicontinuity and local constancy of
the Euler characteristic use that model and its actual comparison maps.

The integration also retains the quotient-linear principal Koszul Ext
calculation and the native differential and exterior-power prerequisites.
The original derived Serre comparison on polynomial projective space over a
Noetherian ring is also proved. Relative duality for general smooth projective
schemes, its canonical-bundle identification and perfect direct image for
general perfect coefficients remain explicit development targets.
These are not consequences merely of naming a dualizing sheaf or constructing
a finite model for a relatively flat sheaf.

Owner reconciliation preserves the existing adjunction maps and main-library
declaration names. Perfect-complex implementations have the single canonical
`Modules.PerfectComplexes` owner; consumed older imports are thin compatibility
entries. The weaker dense-affine results belong to `Properties.DenseAffine`.
The two affine global-section comparisons retain their distinct native
adjunction normalizations. Public consumers check the mixed interfaces.

Validation is scoped to modified Lean leaves, their required dependencies and
focused public consumers. The 84 author-header repairs each have an exact-leaf
compile receipt and preserve the complete body and original provenance.
The merged source-only suite checks 1112 production modules, 23 trust-test
modules and 99 Python regressions, including generated exports, layout,
placeholder and source-policy checks. This integration does not claim a fresh
aggregate library build, complete CI run, downstream acceptance or additional
whole-library kernel replay.

## Previous accepted migration checkpoint

That earlier source checkpoint contains 625 production modules and 23 trust-test modules.
The normal public export and four focused clients pass under the pinned Lean
and Mathlib versions. Native Lake artifact transfer reuses the accepted producer
artifacts: all 693 advertised artifact pairs for the 99 selected source/test
modules match. The production cache export covers all 625 modules.

| Group | Accepted scope | Downstream boundary |
| --- | --- | --- |
| Pointwise and affine suppliers | Twenty producers and the finite-locally-free test; actual fibre/rank, differential, constants, affine base-change and generic-field interfaces; accepted naming and kernel-type correspondence. | R5 consumer refactoring is in progress. Nineteen checked equalities and independent review prove the fifteen old Spec-map correspondences; their four actual callers still need transport. |
| Cartier and ideal geometry | Thirty-nine producers with exact source correspondence, producer checks and independent review; current naming dependencies, actual comparison maps and explicit flatness/finiteness hypotheses are retained. | Original R5 application and producer cuts need coordinated cleanup and focused client checks. |
| Coherent restriction and localization | Thirty-three producers, 119 explicit declarations, seventeen canonical reuses and one consolidated duplicate; complete ordinary review includes all 57 mathematical dependencies. | Quillen's general implementations and application interfaces need the corresponding native retarget. |

Focused producer compilation, declaration/style lint, defining-origin axiom audits
and independent ordinary review cover these groups. The eight reviewed prose
qualifications change no operative Lean code; only their eight source leaves
were recompiled. The coherent source record preserves the original native
packet, its inherited cache provenance, six baseline comment-only transitions,
and the accepted prose addendum. Detailed identities and scoped evidence are in
[the current group projection](migration/pointwise-cartier-coherent.json).

The coherent quotient equivalence retains `IsNoetherian X`; lower subobject and
fullness results keep their locally Noetherian conditions. Cartier results keep
their separate finite, flat and locally finitely presented hypotheses. On that earlier source basis, proper module-cohomology finiteness and
relative locally free cohomology base change remained explicit inputs. The
cohomology integration described above supplies the former; the full arbitrary-base
locally free base-change family remains a separate boundary.

The earlier checkpoints `f87a691813bc5f763dd7a119990c298b35c389f4` and `451aeda`
retain their original source and validation bases. Current normal export checks
do not claim complete downstream acceptance, CI success or additional full
kernel replay. The classified general-source inventory is also broader than
these completed migration groups.

## Complete general-theory source review and placement correction

The source review has classified all 1309 source files under the Quillen
`AlgebraicGeometry` tree and all 1136 R5Lab source files in the recorded input snapshot, including
general theory hidden under curve and K-theory owners. Each file has a fixed
source hash and a reason for migration, splitting, upstream reuse or retention.
Necessary general prerequisites outside these trees are tracked separately;
this is not an exhaustive review of Quillen's unrelated topological theories.
The supplied R5 foundation inventory provides existing-code candidates. Its
future formalization plan is outside this migration.

The earlier extraction selected useful dependency groups but did not complete
this whole-source review. Generality under the criterion in [SCOPE.md](SCOPE.md),
rather than current downstream demand, now controls admission. The placement
review also corrects whole-family names and separates general lower statements
from stronger or specialized owners; [ARCHITECTURE.md](ARCHITECTURE.md) and
[NAMING.md](NAMING.md) record the rules.

Snapshot `451aeda6b8bb5b44402b574dd6cf60f912360f8c` has the scoped acceptance
recorded below. Subsequent organization and migration work changes its source
surface and requires current affected-module validation. Native build artifacts
and valid prior evidence are preserved; the source review is not a claim of
fresh compilation, whole-source migration completion or missing theorem proofs.

## Dependency order for extraction

This order describes dependencies, not a list of wholly unimplemented families.
Several suppliers in the table are now implemented; their current interfaces
are recorded in the family guides and the current-source table above.
Migration includes existing proofs and constructions, their actual canonical
maps and the necessary general prerequisite closure. A theorem-family input is
not counted as its implementation. Exact upstream interfaces are reused;
mixed application files lose only their admitted general cuts.

| Layer | Existing source material to integrate | Acceptance boundary |
| --- | --- | --- |
| General foundations | Small exact categories, Ext1 extensions, K-injective Hom and adjunctions, bounded projective and localization machinery, local flatness and finite-presentation approximation | Native categorical and ring/module objects, with every original universe and hypothesis |
| Module sheaves and complexes | Arbitrary-site helpers, pullback–tensor maps, local free bases, flat resolutions and models, ordinary restriction, extension by zero and derived functors | The original sheaves, functors, adjunction mates and unit/counit equations; no perfect or coherent hypothesis on a general statement |
| Coherent theory | General coherent extensions, localization, Serre quotients, finite support and finite-length stalk functors | The stated Noetherian, finiteness and support conditions; subsequent K-group identifications stay downstream |
| Perfect and derived theory | Intrinsic derived-perfect objects, local lifting and homotopy, affine comparisons, open gluing, supported restriction and qcqs extension up to a retract | Keep chain categories distinct from derived subcategories, preserve explicit bounds and compactness, and assert no global strict representative |
| General geometry | Finite-etale categories, descent and fundamental-group interfaces, normalization and DVR completion, standard functorial constructions, general Picard and Cartier prerequisites | Arbitrary bases subject to the source hypotheses; curve, genus, degree and arithmetic endpoints remain downstream |
| Existing supplier proofs | Pullback–tensor isomorphism, affine module base change, local-basis fibre dimension, finite-flat local freeness, smooth differential rank, proper constants and fibrewise regularity | Implement the existing general producer on the native interface; do not treat a declared input family as a proved result |
| Downstream consumers | Quillen and R5Lab imports, declaration names and dependency pins | Replace old implementations, remove duplicates, then compile the changed modules and their actual affected consumers |

Each closed group records its source correspondence and focused validation
before another group depends on it. Family READMEs document the interfaces,
mathematical results and retained inputs. This file coordinates the groups;
source-only classification and extraction do not count as compiled acceptance.

## Earlier accepted producer groups

The general Ext1, K-injective/adjunction and flat-resolution producers have
passed focused compilation, declaration/style lint, defining-origin axiom
checks and independent ordinary review. The generic/topological Cech split and
the lower site/module ownership corrections have the same scoped acceptance.
R5's former Ext1 implementations have been removed and its two direct consumers
retargeted and compiled. Native Lake cache transfer reuses the accepted Aglib
producer artifacts in R5 without recompiling those proofs. This closes that
consumer group, while the remaining downstream groups retain their own checks.

The arbitrary-base fibrewise regularity and principal-quotient flatness group
has passed those producer checks and independent review. Its public theorem
keeps flatness, finite presentation and all-prime residue-fibre regularity, with
no Noetherian or reduced-base premise. Removal of an unused local-ring premise
from one auxiliary lemma is recorded separately from the unchanged root type.

The thirteen local/derived perfect-complex producers have passed focused
compilation, declaration/style lint, defining-origin axiom checks and independent
ordinary review. Their intrinsic derived-perfect category is distinct from the
chain category; local strict models do not assert a global strict representative.

The local-algebra and generic-normalization producers, the two new
formally-unramified rigidity results for arbitrary local residue targets, and
the generic short-exact-sequence transport helper have the same scoped
acceptance. Their sixteen producer modules preserve the source hypotheses,
universes and actual maps. The helper's actual Quillen consumer also compiles
and has accepted independent ordinary review; whole CI and its memory fit remain
separate checks.

The canonical tensor and pullback group has the same scoped producer acceptance,
including six independently inspected actual-arrow comparison proofs and its
original rank-one/Picard consumers. Its general maps live below those consumers.

The twenty-one D-minus flat-model producers have accepted focused native
compilation, declaration/style and origin/axiom checks, and independent ordinary
review on their recorded final source guards. The subsequent pointwise, coherent
and Cartier waves are recorded in the earlier migration checkpoint above;
their later native/review states do not retroactively alter these earlier
accepted input identities. A native producer pass alone does not supply
independent review. These are
successive closed groups, not a completion claim for the whole migration.

## TT and finite-etale snapshot before the complete review

The TT and finite-etale cuts admit general algebraic geometry and related algebraic, categorical and homological theory from the TT archive and R5 sources. Specialized curve, projective-line, Waldhausen and K-theory applications remain downstream. Their recorded source-correspondence snapshots are linked from the [documentation index](README.md); the historical extraction counts below are not an inventory or validation claim for later additions.

The seven-leaf native structural perfect-complex core and the three homology leaves split among quasicoherent modules, ordinary complexes and perfect complexes have accepted independent review on their recorded inputs. They use actual cochain complexes and the standard native derived category. Strict perfection bounds finite locally free terms; local perfection supplies local derived strict models. Quasicoherent homology and local homology bounds hold on arbitrary schemes, while a single global homology interval retains `CompactSpace X`. No global strictification is asserted. The [perfect-complex guide](../Aglib/AlgebraicGeometry/Modules/PerfectComplexes/README.md) states these distinctions.

The admitted general cuts also include signed mapping cones, selected exact-functor and full-subcategory pushouts, sequential colimits and sign correction, integer-base interchange, polynomial/Laurent coordinates, and canonical tensor/unit/Godement comparisons. The R5 general finite-etale cut supplies the actual finite-etale category, field-valued fibres and base change, together with the weaker finiteness results for field-valued lifts through finite morphisms. Its algebraic and scheme section-rigidity leaves have successful focused producer and declaration/style-lint checks, accepted independent review and a scoped two-declaration permitted-axiom audit. The [interface guide](INTERFACES.md) routes their exact premises to their family owners.

The earlier recorded TT/finite-etale acceptance reconciled 35 production leaves and 14 focused clients with their successful source and artifact identities. The four import facades changed since the preceding check compile; unchanged facade evidence is reused. Native declaration lint, official style, compiled inventory and enrollment, and all 99 source-only regressions pass on 443 library modules and 23 trust-test modules. Scoped producer-origin audits and independent ordinary reviews cover the admitted mathematics. Affected Quillen and R5Lab dependency-graph validation remains in progress; these Aglib checks do not establish downstream completion or a fresh complete kernel replay. Supplied theorem-family inputs remained explicit on that earlier source basis. These historical counts do not describe the proposed next checkpoint.

## Historical first-extraction plan

The first extraction built an independent `Aglib` Lake package with modern `Aglib` module identities. Its first integrated surface contained general commutative algebra, arbitrary-dimensional schemes, module/coherent sheaves, line-bundle objects and general cohomology. Curve/P1/genus/degree/Riemann–Roch and K/G/Q/S applications stay in their source packages.

The historical source basis was R5Lab `95a3772b895fbc19a81684be4ffd519d0fdcd6b3` and the authoritative local Quillen release `189a8e779f0c68b2dfc6f8195daebb3e684a5905`, Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. All 133 initially selected Quillen sources are byte-identical to the initial `83629578a3d70787d41ec631f5234af8758716af` extraction. New general results are admitted by inspecting their full hypotheses and dependency closure. Aglib is the import root. Declaration namespaces use native mathematical owners and collision-safe subjects under the user-authorized refactor, while preserving exact hypotheses, canonical maps and explicit theorem-family parameters. Original source repositories were read-only for that staged extraction.

### Parallel ownership

| Workstream | Source and implementation ownership | Consumer |
| --- | --- | --- |
| Package integration | Lake files, dependency/runtime setup, work plan and whole-package integration | All source families |
| Checks and generation | scripts, production/test entry facades, origin audits, structural/visibility/source checks and interface fixtures | Independent package acceptance |
| Ring theory | R5 general RingTheory and Quillen regular-local prerequisites, generic localization-length support | Smooth geometry and module operations |
| Category and homology | Quillen exact/abelian/small-model and homology support | General sheaf and coherent operations |
| Scheme operations | Quillen general sheaf/coherent/vector-bundle functors and required finite-module support | Coherent cohomology |
| General geometry | R5 lower scheme/rank/field definitions, smooth/normal/differentials and generic Picard | Cohomology and original general APIs |
| Cohomology | R5 general cohomology, general CurveEuler and first-quadrant/Ext/Noetherian support | General scheme cohomology consumers |
| Latest Quillen scheme theory | General module tensor, base change, Godement resolutions and derived operations, with application-independent closure | General sheaf and cohomology clients |
| Latest Quillen general cuts | Precisely selected general declarations under application directories, with minimal lower helpers | qcqs induction, ordinary complex support and canonical-unit comparisons |
| Documentation | Colocated subfamily mathematical/API guides and doc/ cross-family guides | Mathematical and package users |

Each implementation author writes only assigned module paths and its provenance fragment. Root Git/index operations and shared entry generation are serial. Other writers are present; preserve their changes and request dependency edits from the named owner. Temporary logs and experiments use separate task directories. Root integration owns mutable whole-package build output; authors receive exact diagnostics and retain proof repair ownership.

### Execution order and acceptance

1. Create the pinned independent package and enforce Mathlib-only production dependencies. Establish modern modules, standard mathlib lint/budget settings, source provenance and generator/check ownership.
2. Produce ring/category/homology primitives in parallel. Extract generic exact/Serre/subcategory/small-model and localization-length support from their Q/K/G application owners.
3. Produce ordinary sheaf/coherent/vector-bundle operations and general geometry/Picard in disjoint paths. Keep group maps and curve-specific consumers outside the package.
4. Connect the actual general cohomology surface to these lower objects. Settle modern export visibility and compile repairs without altering assumptions or conclusions.
5. Generate complete entry facades, build admitted source and positive clients, replay source enrollment/origin audits, run structural/style checks and kernel replay on the identified complete source basis.
6. Verify standalone usage and document exact remaining premises and coverage. Compare source identities and preserve original repositories. Update this plan with the accepted surface and any real unresolved work.

Every occupied source subfamily owns a README describing objects, interfaces, mathematical conditions, canonical maps, focused imports and current consumers. Root doc/ owns scope, source/dependency provenance, cross-family routes and development checks. Documentation does not establish proof closure; retained standard inputs remain explicit.

The user fixed the root module as Aglib, requested Mathlib/Stacks/monograph-informed architecture, and authorized interface redesign and large refactoring. The canonical namespace policy is in ARCHITECTURE.md and namespace-map.json. Checks on earlier module identities do not establish acceptance of the final source surface.

The maintained extension rules live in `ARCHITECTURE.md`; `NAMING.md` distinguishes module paths, native namespaces, object types and declaration names. Parent context supplies the subject: `Morphisms.Finite`, `Morphisms.Smooth`, `Modules.Coherent`, `Modules.QuasiCoherent`, `Modules.LocallyFree`, `Modules.Invertible`, `Modules.Differentials` and `Modules.Flat`. Actual mathematical objects retain their meaning, including `Scheme.CoherentSheaf` and `StructureSheaf`. Exact Mathlib spellings such as `CochainComplexPlus` and `RightDerivedFunctorPlus` are retained. Helpers belong to their mathematical owner rather than their first application; generic ring-homomorphism properties and closed-source Noetherianity are routed accordingly.

### Integration history on earlier source bases

The original 221 extracted implementation modules have been reorganized by mathematical subject, with semantic splits and native namespaces. The source skeleton follows Mathlib's RingTheory, Algebra, CategoryTheory, Topology/Sheaves and AlgebraicGeometry families. Scheme module operations share one object layer; finite-type quasicoherence, finite presentation, coherent exactness, local freeness, invertible sheaves and differentials have distinct interfaces. Scheme cohomology is collected in one family. Intrinsic scheme properties and morphism properties have separate owners.

The substantive interface work separates the arbitrary-scheme finite-type quasicoherent category and finite direct image from locally Noetherian coherent exactness, moves presentation transport below its consumers, connects the two existing finite local-basis interfaces by a proved bridge, and separates general support/dimension arguments from Noetherian filtered-colimit results. New general sheaf tensor operations own the canonical implementation shared by line-bundle wrappers. Conflation-preserving exact functors live under `CategoryTheory.ExactCategory` to distinguish their meaning from Mathlib's bundled finite-limit/colimit interface.

The earlier local Quillen delta had complete applicability ledgers for 71 Scheme paths and 315 PerfectComplexes paths. That Scheme extraction had 111 new implementation leaves and three existing-category reuses; ordinary homology added 12 leaves. Twenty further precise general cut groups contained 91 source declarations, extracted into 22 destinations with minimal general prerequisites. Existing canonical APIs are reused where they already express the same result. These counts describe source coverage, not final build acceptance. Specialized curve, projective-line, Waldhausen and K-theory applications were not imported wholesale.

The complete pre-rename build passed on 409 production modules and eight positive clients. Declaration lint then identified missing declaration documentation, non-normal simp rules, three data/instance names and two unused arguments. These findings have been repaired against the actual statements and canonical maps. The guarded coherent alias keeps its locally Noetherian premise; its documented unused-argument exception preserves that semantic boundary. Prior producer checks are historical after source repair and the user-selected root rename.

The contextual naming pass moved 108 existing source modules and reconciled current destination paths, names and hashes while preserving original source identities. Obsolete module outputs were quarantined rather than relabeled. The four independent general cuts and the refreshed whole library compile under their current names. Finite-type pullback along `f : X ⟶ Y` lands on arbitrary `X` below the guarded coherent pullback, retaining the Noetherianity of `Y` used by its actual proof. New lower proof owners avoid importing the coherent layer merely to establish finite presentation.

An earlier accepted snapshot contained 411 production modules, eight positive clients and AuditSupport. Its complete local route, 6383-declaration production audit and 420 root replays passed on their recorded source/artifact basis. Subsequent execution fixtures verified warm, version-only, affected-source and compiler-change behavior. The original source-correspondence check covered 476 records from 378 files, and documentation checks covered 830 local links and 118 occupied source families. Those historical records retain their original identities; the later integration record for that extraction is [migration/integration.json](migration/integration.json).

The hosted CI route has declared library/client coverage using native incremental builds, tests, lint/style, axiom auditing, rejection controls, inventory checks and a downstream build/audit. Normal local work, including merge and publication, must use the [incremental validation policy](DEVELOPMENT.md#local-verification-and-ci), retaining compatible evidence and filling only actual affected gaps. Required library/client replay coverage may reuse compatible existing records; publication does not request a new blanket replay. The maintained workflow owns its runner and resource settings; machine-specific local settings are not repository policy.

The CI execution repair replaces repeated per-module Lake invocations with one ordinary build graph and records expected cold-cache probe diagnostics separately. Its 92 source regressions passed on that execution snapshot. Isolated actual builds verify cold, warm, version-only and affected-source behavior, on the recorded execution basis. Both native CI linter commands pass on the same pinned mathematical sources; only their tool prerequisites are built. Original dependency-cache identities and root proof artifacts remain unchanged. These local results validate the execution change; the hosted runner's result is tracked separately.

The subsequent documentation update makes `AGENTS.md` a short action guide, places detailed contribution rules in `doc/`, and rewrites the root README around installation, examples, results and interfaces. Aglib is now public. All 428 tracked Lean files at that snapshot credit `kangxyz`; 157 author lines were normalized and two negative-control headers added. Exact comparison confirms no declaration or proof-body change, original source hashes remain intact, and present destination hashes are refreshed. The 92 source regressions, the exact README Lean example and pinned Mathlib style pass; 102 edited-guide links and anchors are checked. Original kernel receipts keep their original source basis, with the header-only transition recorded separately in [migration/integration.json](migration/integration.json).

The earlier Quillen integration required the original general cone-map additivity law as a public interface. Its single implementation now lives in `MappingCone.Map` as `CochainComplex.mappingCone.map_add`, with the original preadditive and binary-biproduct assumptions; the identity-cone functor reuses it under its unchanged abelian assumptions. Independent ordinary source/mathematical review, actual narrow compilation and an external modern-module generic consumer pass. The public signature and its three allowed axioms are checked. The resulting enrollment contained 412 production modules, nine positive modules and audit support. At that recorded snapshot, the complete source default route exited zero: all 96 source regressions, compilation and positive tests, declaration/style lint, the 6384-declaration production axiom audit, rejection controls, compiled inventory, all 422 root replays and independent downstream build/audit/replay pass. The root replay inventories contain 6431 constants and 14 vacuous modules. The three downstream replay inventories are empty, so their additional replay is vacuous; their compilation and 337-declaration audit exercise the public interfaces. Completed current-basis receipts retain their original execution profiles, and all owned groups for that snapshot were closed. Dependency builds use owned cache copies.

The public-hosted CI recovery addresses an actual three-hour timeout without a Lean compilation error. The workflow uses the public Ubuntu runner and explicit cache restore/save actions. Dependencies save after successful acquisition; immutable run/attempt project generations preserve eligible partial outputs after later check failures. Package version changes preserve incremental reuse. The current cache policy retains outputs despite advisory wrapper-stamp changes, prunes obsolete owned modules and lets native Lake `--rehash` validate actual traces; see [CACHING.md](CACHING.md). These changes pass all 96 source regressions. Hosted execution is assessed from the actual workflow result.

Revision `419bd685cee21ac408756fbfe99565be19d186fd` passes both the [cold hosted run](https://github.com/kangxyz/aglib/actions/runs/38711518878) and a [second run of the same revision](https://github.com/kangxyz/aglib/actions/runs/38724351327). The second job completes in 270 seconds, restores both dependency and project caches, and reports that the library and independent client need no compilation. Both runs save their project-cache generations. Version-only reuse remains covered by the isolated local fixture; these hosted checks do not change the package version.

The completed checks apply to the recorded source and artifact basis. Supplied mathematical premises remain explicit parts of their theorem statements.
