> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#placement-edits-in-widely-imported-modules) · [Context](original-context.md) · [Case index](README.md) · [Previous record](late-lint-repairs-and-dependency-invalidation.md) · [Next record](values-at-concrete-fibre-products-over-spec-commringcatof-a.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

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


## Surface-resolution invalidation follow-up, 2026-11-03

Against pre-integration main `1b737dca122694a54850316097a7ee87ddcbaead`, published tip `5901a32bb9a4c91482ef2cf29de4a3ab61f954b8` changed 70 existing production modules and added 431. Its closed reverse import DAG affected 3,160 modules, including 2,729 existing modules; the changed affine `Sections` provider alone had 2,849 affected modules. The immediate correction compared to the published tip affected 2,992 modules. These are graph counts, not compile times.

An intermediate uncommitted source-freeze snapshot, `impact-source-freeze-public.json`, reports 522 affected modules: 75 existing and 447 new, among 9,388 total modules. It reports 26 modified existing modules, including seven aggregates. These counts apply to that graph snapshot, not a later edited tree.

The `project-cache-recovery.json` inventory identifies matching original-source mappings and artifacts in the shared native cache for 35 old providers; three depend on the changed `AffineRow`. These are cache candidates, not verified hits or checks. At that intermediate observation, build, lint and axiom audit were pending. The source-only policy check had passed (run `272a578b…`) and a 63-terminal build was running; these statements describe that snapshot, not the final repair.

Before adding or moving a helper, inspect the reverse import DAG against pre-integration main, retain an unchanged original producer where possible, and put the additional API in a focused leaf imported by actual consumers. A successful warm-tail compile on an already populated integration graph does not measure invalidation from shared main.


### Final repair and validation

The [complete follow-up case](cases/surface-invalidation-20261103/README.md)
records the final source digest, exact preserved providers, graph and validation.
Relative to pre-integration main the final closure is 518 modules: 73 existing
and 445 added. Source policy, entry/style checks, all changed implementations,
actual affected internal consumers and six relevant in-package test modules
passed. Two coarse lint environments cover all 511 affected implementation
modules and 7800 declarations with no findings; both pinned axiom audits passed.
The final 61-terminal build used zero compiler frontends after valid earlier
outputs were retained.

Retain the previous-commit cache and let native input-key matching choose valid
artifacts. Source restoration does not justify blindly overwriting outputs when
dependency keys differ. Twenty-one of 39 checked restored providers had exactly
the old `1b737dca` native keys; the remaining 18 had current keys. No cache was
cleared, and no cache export or upload was needed. The immediate correction from
the already published tip has a larger invalidation graph than the repaired
migration against its pre-integration baseline; report both honestly.
