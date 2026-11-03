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

