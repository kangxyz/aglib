# Diagnosis and evidence

Return to the [performance lookup](../PERFORMANCE.md).
Ordinary repair uses existing feedback, relevant recorded methods and the
incremental build. Profiling, probes and controlled timing investigations are
separate explicitly requested diagnostics.

## Locate the actual expensive phase

For a requested investigation, select the implicated declaration or module on
its pinned source and prepared dependencies. Keep its actual compiler/options
basis and isolate diagnostic outputs in scratch. Current executable syntax
belongs to [development](../DEVELOPMENT.md) and the selected operating guide.

Separate imports, elaboration, instance synthesis, tactic work, kernel checking,
lint and output serialization. A short `rfl` can still require expensive
conversion of its type. The kernel can also compare proof types when using
proof irrelevance; this does not make a particular kernel-mechanism attribution
automatic.

Use selected native profiler frames and counters for the identified question.
Unfolding counts are not per-constant times. Large printed expressions and the
instrumentation itself can exhaust diagnostic resources.
[Original phase observations](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#what-the-measurements-establish),
[pinned kernel source](https://github.com/leanprover/lean4/blob/v4.34.1/src/kernel/type_checker.cpp).

## Use a faithful probe

Type formation and checking a value or proof can have different costs. To
inspect the original proposition `P` as a theorem type, the recorded probe used:

```lean
theorem probe (_h : P) : True := True.intro
```

A value definition `def probe : Prop := P` can invoke nested-proof abstraction
and measure a different construction. In the Cartesian investigation, the
earlier value probe's 73-second result did not establish intrinsic formation
cost of the theorem type; the corrected theorem-binder kernel check took
7.55 seconds.
[Original probe and conditions](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#a-focused-diagnostic-procedure).

A failed profile or deliberately incomplete scratch probe is not accepted
compilation/proof evidence. Historical replaced-body or skipped-kernel probes
do not belong to ordinary repair or validation. Match any diagnostic's claim
to what it actually executed.

## Search upstream references

If existing experience does not cover the failure, search the affected
upstream GitHub issues, PRs, discussions, official documentation and linked
author reports. Start with Lean and Mathlib, then the affected library. Use
the diagnostic, public declaration, expensive phase and version, with and
without version terms. For example:

```text
repo:leanprover/lean4 is:issue "maximum recursion depth"
repo:leanprover-community/mathlib4 is:pr "synthInstance"
```

Use [GitHub search qualifiers](https://docs.github.com/en/issues/tracking-your-work-with-issues/using-issues/filtering-and-searching-issues-and-pull-requests)
and include open and closed results. Read the reproduction, proposed code and
discussion, then inspect the implementation/release containing the repair
against the pinned source. A similar title or merged PR is a lead, not proof
of applicability.

Existing conditional leads include
[`simp -implicitDefEqProofs`](https://github.com/leanprover/lean4/issues/14331),
[`as_aux_lemma`](https://github.com/leanprover/lean4/blob/v4.34.1/src/Init/Tactics.lean#L13-L18),
and [regular reduction hints](https://github.com/leanprover/lean4/blob/v4.34.1/src/Lean/Declaration.lean#L17-L47).
Choose one only for a matching diagnosed boundary. The earlier eta-before-delta
and wrapper-unfolding discussions were inspected on 2026-10-16; their then-current
issue states are historical.
[Original leads and limits](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#methods-and-evidence).

## Interpret existing evidence

Retain the source/dependency basis, effective options, observed outcome and
scope that matter to the lesson. Existing cases mostly used Lean 4.34.1 and
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`; their exact conditions
remain case-specific. Moving these notes supplies no new measurements.

- A repaired-module pass establishes that pass. A failed baseline supplies no
  successful speedup ratio; a generic provider pass does not cover its consumer.
- Successful unchanged frontends can remain useful in an interrupted or failed
  graph; they do not make the graph, CI or later changed source succeed.
- Keep matched unprofiled timings, profiled observations, unmatched runs and
  author reports distinct. Missing logs or source variants weaken reproducibility.
- Inclusive/asynchronous profile weights can overlap; do not sum them into
  wall-time percentages. Thresholds omit smaller frames.
- Parallel module durations do not sum to whole-build wall time. Extraction can
  move work, and a cached module has no new timing.
- Compiler, lint/axiom, transport and mathematical-correspondence evidence have
  different scopes. Independent mathematical review and writing acceptance
  retain their existing requirements.

Only a requested speedup comparison needs a matched timing comparison. Match
the relevant source/dependencies, threads, effective flags, output generation,
cache treatment and measurement mode, and account for affected consumers when
work can move. Successful repairs may still be recorded honestly without a
speedup claim.

The complete prior Aglib record is retained at
[`d578d2cb`](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md).
Topic cases link its precise sections. This is a recoverable historical record,
not a second current procedure. Older source/run paths mentioned there have
not been rechecked for availability. Historical commands and then-pending
consumers retain their original date and coverage; current operating/status
owners govern present work.

Update an existing topic when a repair adds an applicable method, condition,
counterexample or limitation. Repeated uses and run chronology need no new
entry. Keep an essential source/evidence link with the case rather than copying
all of its logs or creating another result registry.
