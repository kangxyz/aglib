> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#picard-pullback-parameterize-the-target-unit-before-specializing) · [Context](original-context.md) · [Case index](README.md) · [Previous record](hilbert-scheme-naturality-rfl-value-lemmas-and-regular-components.md) · [Next record](transport-section-equivalences-before-specializing-the-qc-pseudofunctor.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Picard pullback: parameterize the target unit before specializing

At Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`,
the concrete scalar-frame rewrite in
[Picard.Pullback](../../Aglib/AlgebraicGeometry/EtaleCohomology/Picard/Pullback.lean)
failed with an implicit-transparency `@Etale`/`MorphismProperty` mismatch.
The selected-build observation is `picard-kummer-02.log`, line 95 of that
failed source; no failed-source digest is asserted.

Use a completely abstract scalar/frame helper with the schemes, arrows, frame,
and both source and target units explicit. Take equality with the pulled-back
source unit as an input, then instantiate once with the original
`gmUnit_sections` equation. The retained `pullbackFrame_scalar_of_eq` helper
preserves the actual `gmUnit` and frame-torsor square; it does not replace the
coefficient morphism by another comparison.

The repaired leaf, source SHA256
`4c17ce8e264be91543524d3d9fed753e3253c33c21105474ab1fa74672098bc8`,
passed in 54 seconds in the existing `picard-kummer-03.log` observation with
the unchanged standard 200000-heartbeat budget. This validates that leaf's
repair only, not the later boundary-naturality, quotient or henselian
consumers. These observations are not a matched performance benchmark, and
no separate probe or resource-budget increase was added.

