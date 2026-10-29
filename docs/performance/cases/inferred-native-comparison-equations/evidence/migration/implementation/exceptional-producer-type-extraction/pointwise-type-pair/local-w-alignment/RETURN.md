# Exact local-W type alignment capture

**No raw alignment to the original producer binder context was obtained.** The exact40dc attribute changes the encoded W proof in all four expected module HasDerivedCategory domains. The probe matched the first six locals, then stopped at the first module-derived-category instance. It did not replace a mismatching class binder.

Actual type-only run `remote-bb747cc06f5c42afa4d707846fdaf411` recorded exit 1 in 6.526s, one frontend. This is an intentional raw-alignment gap, not an API/syntax error. Frozen65bc/setup922/providerb8a/default resources remained unchanged; managed-source and frozen-context mutations are zero.

The attribute is exactly `attribute [local instance] CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard`, immediately after local hasSheafifyLarge and before all variable/HasDerivedCategory/K/native goal types. The b49 formation expression and its h substitution are unchanged.

Here “standard” denotes `CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard`; “generic” denotes `CategoryTheory.GrothendieckTopology.instWEqualsLocallyBijectiveOfHasWeakSheafifyOfHasSheafComposeOfPreservesSheafificationOfReflectsIsomorphismsForget`. Counts are unique raw constant nodes, without unfolding.

| Captured raw expression | Standard | Generic | Structural DAG nodes |
|---|---:|---:|---:|
| Actual inferred output | 1 | 0 | 1248 |
| Controlled closed literal goal (_h, index20) | 1 | 1 | 1942 |
| Controlled closed K domain (index19) | 1 | 0 | 41 |
| Original actual K type | 1 | 0 | 41 |

| Closed HasDerivedCategory domains | Producer W head / nodes | Controlled expected W head / nodes | Raw structurally equal |
|---|---|---|---|
| Module X, S, X', S' (indices6–9, each) | generic / 445 | standard / 39 | false |
| Ab X, S, X', S' (indices10–13, each) | neither / 51 | neither / 51 | true |

For each module domain the first raw difference is `root.arg[2].arg[5].head`: argument5 of the encoded SheafOfModules.instAbelian datum, with producer generic W head and controlled expected standard W head. Generic universes are `[u+1,u+2,u,u+1,u+1]`; standard universes are `[u+1,u]`.

Expected and producer closed binder domains were captured before ANY expected alignment/substitution. The closed expected K and `_h` domains were also retained before substitution. Their deBruijn indices and binder ordinal/name lists remain explicit in the capture. Matching ordinal contexts are used only for the closed HasDerivedCategory raw comparisons.

Local indices0–5 (Λ, Ring, X, S, X', S') have raw alpha/structural match flags true. At expected index6, local-instance lookup reports `No raw-type-matching original local instance`. No aligned EXPECTED proposition, post-alignment alpha/structural flag, or post-alignment first-difference result was produced. The closed expected goal is not presented as a same-context proposition.

The K rows have the same W-head counts; no full K-type alignment claim follows after the earlier binder gap. The controlled closed literal goal still contains both named W heads. These observations do not establish definitional inequality, timeout causation, or a fix.

| Raw payload | SHA256 |
|---|---|
| ACTUAL | `5adee118760dd4f72eafbcd8bed5b4574d4c9fa6c5364d6d1a3705402e71f450` |
| EXPECTED_CLOSED_BINDER_20 | `d453b34afa0ee3f6546c39471fe5982f0768e77a90033d951d03835d0e06849d` |
| All other captured binder graphs (bundle) | `cd2ad7fc0174b82a68829dfd9721273090d63ef7edd73cfd6d8b0d045e1464e2` |

Actual raw type: `/Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025/migration/implementation/exceptional-producer-type-extraction/pointwise-type-pair/local-w-alignment/ACTUAL.rawexprdag.txt`.
Closed expected goal: `/Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025/migration/implementation/exceptional-producer-type-extraction/pointwise-type-pair/local-w-alignment/EXPECTED_CLOSED_GOAL.rawexprdag.txt`.
Closed/native binder bundle: `/Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025/migration/implementation/exceptional-producer-type-extraction/pointwise-type-pair/local-w-alignment/CLOSED_BINDER_TYPES.rawexprdag.txt`. Individual block hashes, byte offsets, node counts, binder names and first differences are indexed in RETURN.json and RAW_CAPTURE_PROJECTION.json.
Context/matching log: `/Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025/migration/implementation/exceptional-producer-type-extraction/pointwise-type-pair/local-w-alignment/CAPTURE_CONTEXT.txt`.

Executed script SHA256: `284bb62ccef2c9827efd5f00f5bd4577485c0b1bcf261866692eb3fcf7b08e44`.
Request SHA256: `5edaf51b9d1f9db88b97178957884070369bf69f03e21cfc52c1447fef31077f`.
Control40dc source SHA256: `40dc37e017e75d865319f968cbb1fe98d44f73f193201655bc0aa78fc46bd471`.
Producer source SHA256: `6a84bc472cb2a3b2841d27fdb753e907371fe633c7d0364fd288518b7a31afbf`.
Provider source SHA256: `65bc75bd87f6942ed330fbc8ccfc98bdf61a14989f0b422a98d87f9a64e91ef7`.
Setup SHA256: `922034a0e8a01bed3cdcc4a09ed1ab37d1fd5b7f6b15d5a3f26e1c8d58a250f5`.
Provider artifacts SHA256: `b8a81d3f1d55c994c43b511c84dec652f6367b2ff9a0ad34d1f9a153192e3bf6`.
Lean 4.34.1; mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Full stdout: `/Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025/migration/incremental-compiler/diagnostics/r4-local-w-type-alignment-bb747cc0/stdout.log` (327546 bytes; SHA256 `6934425648a8ca45a55fd9655ad75c09004470c115ebb326ce070e2b1b16cdef`). Exact native argv/cwd/profile/receipt/source archive are recorded in RETURN.json.

Mechanical local reproduction, using only the existing stdout:

```sh
python3 "/Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025/migration/implementation/exceptional-producer-type-extraction/pointwise-type-pair/local-w-alignment/capture_projection.py" \
  "/Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025/migration/incremental-compiler/diagnostics/r4-local-w-type-alignment-bb747cc0/stdout.log" \
  "/Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025/migration/implementation/exceptional-producer-type-extraction/pointwise-type-pair/local-w-alignment"
```

No further native run, raw type forcing, normalization, proof erasure, theorem/proof-body access, Meta.isDefEq, profiling, kernelPointwise rerun, model change, source repair or production closure is claimed. The previously reported40dc kernel failure remains separate evidence; this type capture does not identify its cause.

Remaining gap: a same-original-context controlled expected output comparison is blocked by the recorded module binder mismatch. The mathematical author owns its interpretation and any repair.
