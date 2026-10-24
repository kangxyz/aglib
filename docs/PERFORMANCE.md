# Lean compilation performance

Use this page to locate a relevant method, then read that topic's conditions
and cases. Detailed experience lives in [`performance/`](performance/diagnosis-and-evidence.md);
current commands remain in [development](DEVELOPMENT.md#local-verification-and-ci),
[caching](CACHING.md#shared-ci-protocol) and the [toolkit guide](../scripts/README.md).

## Find a relevant method

| Observed problem | Topic |
| --- | --- |
| `whnf`/`isDefEq`, expensive concrete map comparisons, dependent transports or rewrite loops | [Conversion boundaries](performance/conversion-boundaries.md) |
| Cheap generic proof but expensive specialization; costly `rfl`, structure field or repeated constructor | [Shared constructions and equations](performance/shared-constructions.md) |
| Instance-search limits, incompatible parent structures or unresolved universe `max` | [Instances and universes](performance/instances-and-universes.md) |
| Unexpected rebuilds, memory limits, checker startup or a leaf that fails when imported | [Build, check and interface costs](performance/build-and-check-costs.md) |
| An explicitly requested investigation of cause or timing | [Diagnosis and evidence](performance/diagnosis-and-evidence.md) |

Key lessons:

- Identify the failing phase from existing feedback. Short proofs and successful
  elaboration can still leave expensive kernel conversions.
- Keep the actual objects, maps, structures and universes. Prove an appropriately
  typed equation before specializing heavy data.
- When that is insufficient, share the actual regular equation or constructor
  across the producer and consumer. More abstraction can also move or increase cost.
- Preserve required component formulas, original hypotheses and actual consumers.
- Reuse compatible artifacts and successful checks. A module pass establishes
  its recorded scope, not a speedup, compiler cause or whole-graph success.

## Repair workflow

For serious compilation trouble, use the lookup above before further
experiments or budget changes. Read the affected dependency's topic when it owns
the expensive construction. Apply a relevant recorded repair with its conditions;
ordinary proof iteration stays incremental under the
[existing source and budget policy](DEVELOPMENT.md#setup-and-focused-builds).

When the recorded conditions do not cover the problem, use the
[upstream reference search](performance/diagnosis-and-evidence.md#search-upstream-references):
search by the actual diagnostic, public symbol, phase and version, then check
applicability to the pinned source. Separate profiling and probes are explicitly
requested diagnostics, not prerequisites for ordinary repairs.

## Keep experience reusable

When a validated repair adds new reusable knowledge, update the matching topic
under `docs/performance/`. Merge repeated experience; retain the symptom,
conditions, effective change, important failed alternative or limit, and existing
source/build evidence. Distinguish observation from a proposed cause.

A new run, another passing module or another application of a known method
needs no entry. Add a topic only for a distinct mechanism that needs an owner;
keep this page limited to key guidance and reading routes. Common methods live
here in Aglib; downstream guides retain their own cases and link to them.
[Evidence and historical records](performance/diagnosis-and-evidence.md#interpret-existing-evidence)
retain the original scope without requiring new builds, benchmarks or acceptance.
