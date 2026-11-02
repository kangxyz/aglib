# Deterministic cardinality and canonical transport of one selected basis

> Historical source-bound record: names, hashes, checks and limits below refer to
> the stated original executions, not a fresh check of the current sources.

Source-bound performance case, integrated 2026-10-31 08:34 UTC.
The ordinary native checks were already completed; this documentation update
does not request a new validation cycle.

## Reusable method

When one selected basis has positive finite cardinality r, but an actual
consumer uses Fin(n+1), first consider the deterministic predecessor n:=r-1.
Prove hn:r=n+1 arithmetically, and transport the SAME basis by native
`Basis.reindex (finCongr hn)`. Return and consume that same transported witness.
This avoids eliminating an unnecessary natural-number existential across the
existing dependent context. The mathematical content, vectors, coefficient
map and root/presentation remain fixed; native `Basis.reindex_apply` identifies
the vectors at the inverse index. No second basis is chosen and no arbitrary
orientation permutation is made.

This source-bound case supports that bounded repair. It does not establish a
unique internal cause of the whnf timeout or a matched performance speedup.
Canonical reindexing alone did NOT pass; retaining an existential successor
witness still timed out. The exact final deterministic version passed.

## Exact condition and invariant

The full production theorem is
`KaehlerDifferential.exists_integralTraceEntrance_of_complete_regular_dim_two`
in `RingTheory/Kaehler/PureDegreePTrace/CompleteRegularEntrance.lean`.
It starts with original complete regular local R, dimension2 and characteristic
prime p, original fraction field K, original purely inseparable extension L/K,
and original `Module.finrank K L=p`. R,K,L have independent universes.

It derives original domain/normality/Noetherianity, finite-dimensionality,
characteristics and finite literal normalization. It retains one native
formal-coordinate equivalence e, the original scaled integral root z=m*b and
coefficient a, the shared same-root field presentation h, and one chosen
finite expanded coefficient-series base E with one integral basis bR.
Its output includes genuine finite type of the literal Lambda→R map and the
actual integral trace-transpose cokernel annihilator. The original R/K/L,
scalar maps, hdegree, e, h, E, a and integral nonzero da never change.

The field-presentation backend, accepted Coordinates supplier, and accepted
Cokernel.of_basis remain unchanged. The final proof uses:

```lean
let n := r - 1
have hn : r = n + 1 := (Nat.sub_add_cancel (Nat.succ_le_of_lt hr)).symm
-- unchanged original coefficient actions and scalar towers
let bR' : Module.Basis (Fin (n + 1)) R (KaehlerDifferential Λ R) :=
  bR.reindex (finCongr hn)
refine ⟨hfinite, hft, bR', hda, hK.trans hn, hdaK, ?_⟩
exact exists_nonzero_annihilator_integralClosureTraceTranspose_coker_of_basis
  Λ R K L n hdegree a h bR' hda
```

The public statement is unchanged by the deterministic repair. Its basis
witness is the same canonical reindex used in the actual Cokernel call.

## Failure and diagnostic chronology

Normal native limits throughout: 7000 MB frontend, 7168 MiB aggregate, one
Lean/build thread, default200000 heartbeats. No budget, transparency setting,
linter suppression, axiom, replacement model or provider edit was used.
Lean4.34.1, Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.

1. Source96a: ordinary scalar/source/target inference mismatch in the cokernel
   predicate. Explicit native R/source exterior/target Hom-bidual pins repaired
   that formation seam (sourceca99). This was not the later arithmetic issue.
2. Sourceca99: proof letI style errors plus separate declaration-level whnf200k.
   Normal local let dictionaries repaired the style errors (source89b); whnf
   persisted. Do not infer success from the linter correction.
3. The one89b full-proof inline diagnostic5e5ff had its own longLine error and
   whnf200k. Durable events reached through original generator/presentation,
   not the next finite-basis marker. This did not distinguish supplier
   inference from destructuring and was not clean diagnostic admission.
4. Original k/R/K pins and retaining inferred hcoeff before destructuring
   produced source4648; normal graph83 still whnf200k. Current4648 diagnostic
   e22ec (6.75 s/2.522 GB) reached BOTH supplier inference and destructuring.
   Therefore the earlier89b boundary was not carried over as current evidence.
5. Current4648 continuation59377 (12.106 s/2.510 GB) reached exactly the marker
   before `obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ...`; no marker before
   outer witness assembly. No admission/style error or guard occurred.
6. Source5551 retained hn instead of rfl substitution and canonically reindexed
   bR. Normal graph93 still whnf200k (own5.8 s). Current5551 diagnosticc289
   (6.55 s/2.527 GB) again reached exactly before the changed `obtain ⟨n,hn⟩`,
   not outer refinement or basis reindexing. This rules out claiming that
   canonical transport alone was the accepted repair, or blaming the later
   cokernel call from those runs.
7. Sourcebf477 replaced ONLY that existential obtain with deterministic n:=r-1
   and actual arithmetic hn. SAME canonical bR reindex and all later code
   stayed fixed. Native graph100 emitted genuine OWN PASS15 s. Whole graph
   ended exit1 solely on unrelated P06/P07 roots; duration29.870789 s,
   peak3060977664 bytes, no guard, owned group gone. Snapshot113 retained the
   accepted source. This is the full theorem, not a prefix or formation probe.

The diagnostics use ordinary production proof behavior, so visited markers
are not proof completion: recovery and revisits must be reported separately.
Every event is appended and flushed, with durable proof-entry visit labels.
The native log and full event chronology are retained. Missing later events
locate a visited-uncompleted command in that exact run, not a unique internal
compiler sub-operation or a monotonic-progress guarantee.

Unexecuted instrumentation variants (bare logInfo, initializer, meta-initializer,
no-init helper) were preserved as unexecuted; they provide no mathematical
or native proof evidence. Executed inline variants strip exactly to their
then-current production source; all later clean variants satisfy line length.

## Exact sources and evidence locators

All paths below are in the preserved cloud workspace, not the user's desktop.

- Accepted sourcebf47720765e0032e15320b6c75e1000a1778175c4c2a50e7184fadd9a8729848.
- Accepted lower Coordinatescd2bc9a6f9e45656097c47f29a98b6b7aadf9915b12621468f8beeda8377615a.
- Accepted lower generator719fae3e2432fa46d642c2a68b5b0559591ab25b1123974a5206242bc7fb0c60.
- Accepted formal coordinates2907f22ec5232ccd8a564b5f1688ba641fa20eeab119b3fbdf6084ddc7fbefaa.
- Unchanged Cokernel903504a6e89d69a83343e4251829fdbd855ed2c219f322df0a2f04e9c8256705.
- `surface-resolution-recovery/native/recovery75.log` through the exact
  selected graph records76/77/83/93/100 retain ordinary failures/passes.
- `surface-resolution-recovery/native/charp-entrance-inline-events.*`,
  `charp-4648-inline.*`, `charp-4648-assembly.*`, `charp-5551-assembly.*`
  retain executed diagnostic logs and capped receipts.
- `surface-resolution-state/charp-formal-entrance/final-caller/diagnostic/`
  retains full diagnostic sources, exact-strip manifests and append-only
  event files for each current source identity.
- `repair01/`, `repair02/`, `repair03-proposed/`, `repair04-proposed/`,
  `repair05-proposed/`, their narrow diffs and before-source snapshots retain
  each bounded edit and its exact original source.
- `ACCEPTED.json`, `STATUS.md` and `REPAIR05-PROMOTED.json` record final identity
  and coverage. No whole-graph, fresh axiom-audit, geometric trace or final
  surface-resolution completion is claimed by this source-bound own pass.

## Preserved portable evidence

The adjacent before/after source text and exact repair diff preserve the
only deterministic-index edit. Native graph100 selected results, source hashes,
log and aggregate receipt are copied in evidence/. The historical full graph
failed on unrelated roots; only the exact entrance own pass is claimed. Earlier
diagnostic sources and logs remain at the recorded workspace locators above.
