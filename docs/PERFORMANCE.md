# Lean compilation performance

This page keeps key guidance. The [case folder and index](performance/README.md)
preserve the complete earlier records, including failed attempts, measurements,
source identities and limitations. Read the relevant case, not the whole archive.

## Key points

- Identify the failing phase from existing feedback. Short proofs and completed
  tactics can still leave expensive kernel conversions.
- Keep the actual objects, maps, structures and universes at the comparison
  boundary. Shared equations or constructors can help; abstraction can also
  increase cost or move it to consumers.
- Preserve original hypotheses and required component formulas. Reuse compatible
  artifacts and successful checks under the existing operating guides.
- A case establishes its recorded result and conditions, not a universal
  optimization, compiler cause or whole-graph success.

## Find a case

| Problem | Original records |
| --- | --- |
| Expensive concrete conversions, fields or repeated proof arguments | [Equation/structure cases](performance/equation-proofs-presentations-and-structure-fields.md), [whole comparisons](performance/whole-module-exchange-comparisons-before-evaluating-components.md) |
| A definition becomes expensive when projected or specialized | [Isomorphism/value comparison](performance/hilbert-scheme-direct-images-compare-isomorphism-values-at-the-iso-level.md) |
| Instance search or universe inference | [Existing preservation dictionary](performance/pass-the-preservation-dictionary-of-an-equivalence-explicitly.md), [universe case](performance/pinning-the-actual-module-universe-in-a-kan-extension-preservation-proof.md) |
| Recursive simplification | [Self-referential equality](performance/picard-tangent-space-prove-additive-group-algebra-abstractly-then-specialize.md#avoid-self-referential-coefficient-simplification) |
| Memory, repeated compilation or checker setup | [Resource observations](performance/remote-resource-calibration-on-the-unchanged-library.md), [dependency overlap](performance/late-lint-repairs-and-dependency-invalidation.md) |
| Cache metadata or handoff | [Shared-artifact metadata](performance/local-validation-and-shared-artifact-link-metadata.md), [dependency handoff](performance/test-dependency-handoff-and-native-resource-limits.md) |

The [full index](performance/README.md) retains every original section in order,
with its [original context](performance/original-context.md).

## Repair workflow

For serious compilation trouble, find a matching case before further experiments
or budget changes, including the affected dependency's cases when relevant.
Use current [development](DEVELOPMENT.md#local-verification-and-ci),
[budget policy](DEVELOPMENT.md#setup-and-focused-builds),
[caching](CACHING.md#shared-ci-protocol) and [tooling](../scripts/README.md) for
present commands. Old command sequences inside case records are historical.

If the case conditions do not cover the problem, search upstream issues, PRs,
discussions and official documentation by diagnostic, symbol, phase and version,
then check applicability to the pinned source. Separate profiling and probes
remain explicitly requested diagnostics.

## Preserve cases

Record a reusable repair in its own file under `docs/performance/`, with its
conditions, failed approaches, effective change and existing source/build evidence.
Update the same case for follow-ups and link it from the folder index.
Refine key guidance here while keeping the original cases and their details;
summaries and Git-history links do not replace the saved records.
Documentation itself adds no build, benchmark or acceptance cycle.
