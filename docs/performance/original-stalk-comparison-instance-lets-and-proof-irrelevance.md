# Original stalk comparisons: instance lets and proof-irrelevant conversion

> Historical source-bound record: names, hashes, checks and limits below refer to
> the stated original executions, not a fresh check of the current sources.

## Original mathematical boundary

The surface canonical-trace consumer needs the original ordinary direct-image
stalk identified with sections over the original local-spectrum pullback. The
constructor composes the native degree-zero derived-image inverse, the existing
higher-direct-image stalk equivalence, and the original H0/sections equivalence.
Neither a finite model of the local ring nor a new base-change map is permitted.

The implicated declaration is
`ordinaryPushforwardStalkSectionsLinearEquiv_apply` in
`AlgebraicGeometry/Cohomology/Duality/Projective/Relative/NormalSurface/Trace/Localization`.
The task baseline was `7d071440653407d30fd41d8dbbafce1673a3039b`, Lean4.34.1,
with the pinned Mathlib dependency. Native limits remained 7000 MB per Lean
process, 7168 MiB aggregate RSS and one frontend/thread. No matched speedup
experiment or separate kernel replay was performed.

## Failed approaches and diagnosis

A typed generic three-equivalence constructor and its normalization law first
built an actual local proof `hfull`. The H0 adapter retained the native bundled
sections target. The source used the same commutative-ring hierarchy and
original pullback instance as the public theorem. Ordinary `exact hfull` still
hit maximum recursion depth at the final conversion.

Normalizing only the own constructor and local names with `dsimp only` did not
remove all local definitions from coercion dictionaries. Recovery217's guarded
comparison found six non-proof differences, with zero pending branches:
local alpha/N values inside instance arguments, and local-let carrier types.
Lean's simplifier defaults to skipping instance arguments. Adding `+instances`
to the **same** restricted normalization list addressed that observed boundary,
without unfolding the original higher-image, H0 or base-change definitions.

Recovery224 then reported that the entire inferred type and target were not
syntactically identical, but its completed proof-aware traversal found zero
non-proof differences and zero pending branches. It compared proposition types
before skipping proof-valued subtrees. This is diagnostic evidence, not a proof
of definitional equality. `exact hfull` still failed with recursion depth.
Earlier comparisons that indexed a presumed Eq without first checking the head
and argument count were invalid and were discarded. Likewise, reaching a
comparison cap while discarding its pending work cannot establish exhaustivity.

## Accepted repair

The production proof retains the typed construction of `hfull` and uses:

```lean
dsimp +instances only
  [ordinaryPushforwardStalkSectionsLinearEquiv, e₀, e₁, e₂, H₀, t, a, b, N, α]
  at hfull ⊢
run_tac Lean.Elab.Tactic.withMainContext do
  let some decl := (← Lean.getLCtx).findFromUserName? `hfull
    | throwError "Missing existing original normalization proof"
  (← Lean.Elab.Tactic.getMainGoal).assign (Lean.mkFVar decl.fvarId)
```

This supplies the already constructed local proof term without repeating the
elaborator's failing final `exact` conversion. It does not construct a new
mathematical proof, introduce an assumption, erase a type, or bypass Lean's
kernel. The ordinary production theorem must still pass native kernel checking
at its full declared type; a failed kernel check would reject this repair.
It is not a general instruction to assign arbitrary ill-typed terms or to use
a custom checker. Prefer ordinary typed equations and precise normalization
when they suffice.

## Evidence and limits

Native recovery226 accepted the complete production Localization module in
58 seconds, with matching post-run source hash (prefix `aa1015`). The source
inventory and selected-pass receipt retain its exact hash. This distinguishes
an elaborator conversion failure from successful normal native theorem checking
for this specific existing proof. It does not identify a universal Lean cause,
prove a speedup, or certify downstream consumers. The actual LocalEvaluation
and AffineEvaluation modules became unblocked and require their own ordinary
checks; no extra acceptance cycle is created by this documentation.
