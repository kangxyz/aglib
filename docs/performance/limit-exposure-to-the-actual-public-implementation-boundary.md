> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#limit-exposure-to-the-actual-public-implementation-boundary) · [Context](original-context.md) · [Case index](README.md) · [Previous record](local-instance-names-must-remain-distinct-across-actual-imports.md) · [Next record](continue-native-checks-after-cache-record-preparation-fails.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Limit exposure to the actual public implementation boundary

An exposed section changes implementation visibility, rather than merely
marking exported names. In `ClosedImmersion.RightAdjoint.FiniteSource`,
adding a module-wide `@[expose] public` scope made private localization
aliases unavailable in exposed implementations. Native `remote-a86527a5`
reported 47 diagnostics, including those missing names and subsequent
elaboration cascades. The original source had already compiled with a
`noncomputable section` and selected explicit exposed definitions.

Retain that original boundary. A focused `@[expose] public section` around
the already exposed `closedImmersionRightAdjointQuotientResolutionComplex`
API satisfies the maintained export convention without publishing private
helpers or changing any definition body, theorem, map or hypothesis. Remove
the now-redundant per-definition `@[expose]` inside that section; the compiler
reports such redundant attributes as errors. The same attribute adjustment
applies to `NormalModificationH1Vanishing` inside its exposed section.

The repaired full FiniteSource `9637db9e` passed in 110 seconds and the
regular-local consumer passed in 13 seconds in `remote-4f9e0c68`; the full
Aglib entry then compiled in 8.3 seconds. These are existing incremental
build observations at the standard budgets. They verify the visibility
repair, not a controlled timing improvement. No new diagnostic or benchmark
was run for this note.


