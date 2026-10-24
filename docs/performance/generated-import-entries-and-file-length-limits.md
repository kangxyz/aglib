> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#generated-import-entries-and-file-length-limits) · [Context](original-context.md) · [Case index](README.md) · [Previous record](whole-module-exchange-comparisons-before-evaluating-components.md) · [Next record](keep-one-representation-of-module-sections.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Generated import entries and file-length limits

[CI run 39951693002](https://github.com/kangxyz/aglib/actions/runs/39951693002)
failed at `2c34f185` because the generated `Aglib.AlgebraicGeometry` entry grew to
3304 lines while retaining `set_option linter.style.longFile 3100`. This was a
source-style failure; completed compilation was saved, and Test/Publish skipped.

The minimal repair sets that import-only entry's `longFile` option to `0`,
following Mathlib's [explicit generated-root exemption](https://github.com/leanprover-community/mathlib4/blob/d13f23b723b8a846827a245b89c10fc7d3f11612/Mathlib/Tactic/Linter/Style.lean#L379-L383).
Imports, ordinary implementation limits and mathematical checks are unchanged.
Under Lean 4.34.1 and the pinned Mathlib linter, a bounded native fixture reproduces
the 3100-line failure, accepts `0`, and still rejects an ordinary file at 1500.
This is scoped linter evidence, not a full-library CI pass.

Topic generation now uses the existing layout command's explicit `--generate
Aglib.Topic` mode. It always writes `longFile 0` for new and refreshed generated
entries; existing generated topics carry the same setting. It does not infer
exemptions from arbitrary proof-file contents.
Generator fixtures cover new and nested topics, source growth, ownership and
retained root/implementation bytes. Native root generation and CI are unchanged.

