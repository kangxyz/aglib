# Slice mate: consume the proved original value

The original native slice mate failed in GitHub CI at
`mate_moduleEtaleSliceUnderlyingIso_inv` while reducing the final `rfl`
argument: `whnf` exhausted the ordinary 200000-heartbeat budget. The later
unknown-constant error is a consequence of that failed declaration. The full
[failed job log](ci-ecca-job-124153743627.log) is retained; its compilation-cache
save and native-output upload succeeded.

The forward comparison is the actual `Equivalence.forwardComparison`. Its
existing producer theorem `moduleEtaleSliceUnderlyingIso_eq_original` identifies
it with the original unit/counit/associator chain. Passing that proved equation
to `mateEquiv_equivalence_comparison` consumes exactly the equality that the
old proof asked `rfl` to reconstruct. All original adjunctions, equivalences,
comparison arrows, arbitrary-ring and etale hypotheses, universe choices and
model choices remain unchanged. No new import, helper, compatibility premise or
budget option is introduced. The [before](before.lean.txt) and
[after](after.lean.txt) sources retain the complete proof context.

The repaired leaf received a fresh ordinary producing frontend on sealed
source `bb2e2d802a93b4164169b0586ba5b04c8ebc0d0d62eee58a416064a7f4144539`,
native run `remote-1c16d780b2a643809e27b31a3f982d47`. It exited 0 in
14.1120529 seconds with `-j4 -M12800` and the unchanged package heartbeat
budget. [The complete started/finished events](native-frontend.json) identify
the actual compiler invocation; this was neither a cache-only observation nor
a raised-budget experiment. The enclosing Curves build was still active at
that handback, so the event does not assert success of that broader graph or
of hosted CI. This is a supported default-budget repair, not a controlled
timing ratio or a unique compiler-cause diagnosis.

[CASE.json](CASE.json) binds the source and seven unchanged immediate
providers; their complete snapshots and the pinned toolchain, package options
and manifest accompany it. All four applicable native final predicates passed: builtin lint, exact-leaf
text style, the full Batteries declaration predicate and the pinned upstream
axiom auditor. The auditor checked 2577 declarations with zero violations and
only `propext`, `Classical.choice` and `Quot.sound`.
[The native check record](CI160-FINAL-PREDICATES.json) and
[closed exit-0 receipt](native-check-receipt.json) retain exact commands, subject
source/artifacts, execution workspace and no-input-drift result; complete logs
are alongside them. These checks read the completed D artifact under managed
resource admission from an idle execution workspace, without changing D source
or restarting compilation. Compatible provider checks are reused. No kernel
replay or separate client check is added.
