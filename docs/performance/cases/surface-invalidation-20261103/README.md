# Surface migration: preserve stable producers

## Source and failure

Pre-integration main is `1b737dca122694a54850316097a7ee87ddcbaead`;
the published migration is `5901a32bb9a4c91482ef2cf29de4a3ab61f954b8`.
Adding two affine section-map formulas to a widely imported existing provider
contributed a reverse closure of 2849 modules. The entire migration changed 70
existing production modules, with 3160 affected modules, including 2729 existing
ones. These are import-graph counts, not measured compilation durations.

A later warm incremental build on the integration workspace did not measure the
invalidation of an earlier shared-main cache. The graph must be checked against
the intended pre-integration baseline before editing a stable provider.

## Repair

The [restored providers](restored-providers.json) match the baseline bytes.
Additional section-map, raw tilde-composition, finite-dimension, normalization,
local-regularity and other API laws live in focused leaves imported by their
actual consumers. Original coefficient constructors and laws remain implemented
once in their original parent; the new import paths reexport that producer.

The unused `Trace/AffineLocal` extraction only exposed facts already present in
baseline `Trace/Core`. It had no actual consumer or genuinely new mathematical
content. Removing it and an unused resolution-helper exposure retains the
original proofs and baseline public APIs. It avoids repeating costly checking
of already existing implementations. The original Core remains byte-identical.

Restoring legacy namespaces exposed two short-name ambiguities. Explicit names
in the new migration consumers retain the intended generic maps without editing
widely imported original providers.

For the new quotient-localization representative equation, a direct application
of `quotientKerEquivOfSurjective_apply_mk` timed out while comparing the outer
quotient-equivalence composite. A full `simp only` left the native factory goal
open. The successful proof simplifies `RingEquiv.trans_apply` and
`Ideal.quotEquivOfEq_mk`, then applies the original representative lemma with
its literal `Away.map` as explicit `f`. Constructors, maps, hypotheses, universes
and budgets are unchanged. This is a bounded conversion-boundary repair, not a
controlled speedup experiment.

## Validation and cache boundary

The final native source digest is
`aebfc416d1eead38f6cf8f313c735cae4ce0d4a5610b72e8ab7ebd377e55c92e`.
The [graph evidence](impact.json) records 518 affected modules relative to the
pre-integration main: 73 existing and 445 added, among 9386 production modules.
There are 24 modified baseline modules, including seven import-only aggregates.
The immediate restorative patch from the published tip has a larger closure;
this is why matching earlier cache inputs matter.

The [validation summary](validation.json) and exact run-result files record:

- Source policy passed on 10262 Lean inputs; native entry and text-style checks passed.
- All changed implementations passed through 61 native terminal targets; the
  final invocation `remote-622965ff792c457d8073651fb0e12843` accepted cached
  outputs with zero compiler frontends.
- Seven additional affected internal-library terminals and six relevant
  in-package test modules passed.
- Two coarse lint environments jointly checked all 511 affected implementation
  modules and 7800 declarations with zero findings. The original enabled
  normal/slow predicates and suppression semantics were retained.
- Both pinned native axiom audits passed with only `propext`, `Classical.choice`
  and `Quot.sound`. Their loaded environments overlap; their counts are not added
  as a unique declaration count.

Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` are
unchanged. The previous-commit cache is retained. Native Lake selects artifacts
by current source/dependency input keys; restored source bytes alone do not prove
that every dependency key matches. A bounded post-check found 21 of 39 needed
restored providers with exactly the original `1b737dca` keys and `.olean`
identities; the other 18 have current keys and must not be overwritten with old
outputs. No `.lake` or shared-cache clearing was performed.

An unnecessary cache-export attempt was cancelled after the user clarified that
prior-commit reuse was intended; it produced no delivery archive, stage or upload.
This repair uses existing native cache reuse. It does not prescribe changing CI
workflows or starting another runner.

The [source scope](source-scope.json) and archived
[DAG analysis script](dag_impact.py.txt) make coverage explicit. All mathematical
exclusions and genuine initial RDP hypotheses remain. No full Aglib rebuild,
kernel replay or separate client check is claimed. Complete native logs are in
the integration's retained task output directory.
