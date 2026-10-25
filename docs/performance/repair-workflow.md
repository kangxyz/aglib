> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#repair-workflow) · [Context](original-context.md) · [Case index](README.md) · [Previous record](original-context.md) · [Next record](ci-cache-reuse-across-dependency-updates.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Repair workflow

For serious compilation trouble, read the relevant findings here before trying
more fixes or increasing budgets. Match the symptom and source/toolchain
conditions; use the affected dependency's performance guide when it owns the
expensive construction.

If the guide does not cover the failure, search the corresponding upstream
GitHub issues, PRs and discussions, official documentation and linked author
reports. Start with Lean and Mathlib, then the affected library. Use distinctive
diagnostic text, public declaration names or the expensive phase (`whnf`,
`isDefEq`, instance synthesis, imports or serialization), with and without
version terms. For example, using [GitHub search qualifiers](https://docs.github.com/en/issues/tracking-your-work-with-issues/using-issues/filtering-and-searching-issues-and-pull-requests):

```text
repo:leanprover/lean4 is:issue "maximum recursion depth"
repo:leanprover-community/mathlib4 is:pr "synthInstance"
```

Replace the quoted terms with the actual symptom; also search this library's
repository and both open and closed results. Read the reproduction, discussion
and proposed code, then check the pinned source and release containing the fix.
Similar wording or a merged PR alone does not establish applicability.

After a repair passes the relevant incremental check, summarize it here:
symptom, affected declarations, versions/conditions, effective change, existing
validation evidence and source links, and remaining limits. Mark an uncertain
cause as uncertain; retain failed approaches only when they prevent repeated
work. Reuse existing measurements and compatible checks; no per-edit diary,
mandatory benchmark or extra acceptance run is required.

