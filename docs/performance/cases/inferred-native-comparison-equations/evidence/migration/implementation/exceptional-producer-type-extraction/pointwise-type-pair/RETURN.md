# Actual pointwise type pair

Native run `remote-d72be55f9df342ea8cb505bb2a6da32e` recorded exit 0 in 8.711s, one frontend, frozen65bc/setup922/providerb8a/default resources unchanged. Managed-source and frozen-context mutation counts are zero.

Actual: `inferType` of the source6a84 producer applied to its original nineteen fvars and K. Expected: the copied b720 formation theorem’s `_h` binder type, with only `sq.w.symm` replaced by `h`. Both are aligned to the same twenty fvars, and neither contains metavariables. No theorem proof body was read.

| Raw type | Structural DAG nodes | Bytes | SHA256 |
|---|---:|---:|---|
| Actual | 1248 | 71343 | `976ededafb405a30dfe66e98d8850c34536c81291ccc81563eb41b61ecda4820` |
| Expected | 1844 | 100900 | `f99d7902338ea8e1fa290b80c8f380096b49069846a2820152993767b2276226` |

Raw alpha equality: false. Raw structural equality: false. These are syntax observations, not a definitional-equality verdict.

First difference under the saved spine-head-first, left-to-right, depth-32 traversal:

`root.arg[1].arg[6].arg[3].arg[5].arg[0].arg[2].arg[5].head`

- Actual constant: `CategoryTheory.TorsionZMod.Ringed.abWEqualsLocallyBijectiveStandard`; universes `[u+1, u]`.
- Expected constant: `CategoryTheory.GrothendieckTopology.instWEqualsLocallyBijectiveOfHasWeakSheafifyOfHasSheafComposeOfPreservesSheafificationOfReflectsIsomorphismsForget`; universes `[u+1, u+2, u, u+1, u+1]`.

This path reaches argument 5 (zero-based) of `SheafOfModules.instAbelian`, inside `DerivedCategory.Plus`. The differing actual instance application has 3 arguments; the expected one has 13. Their common first three heads are `Scheme.Etale`, `Scheme.instCategoryEtale`, and `Scheme.smallEtaleTopology`. The complete argument IDs, heads, levels, and path walk are retained in RAW_PAIR_PROJECTION.json.

| Prefix transition | Raw head on both sides |
|---|---|
| `root` | `Eq` |
| `root.arg[1]` | `CategoryTheory.CategoryStruct.comp` |
| `root.arg[1].arg[6]` | `CategoryTheory.CategoryStruct.comp` |
| `root.arg[1].arg[6].arg[3]` | `CategoryTheory.Functor.obj` |
| `root.arg[1].arg[6].arg[3].arg[5]` | `CategoryTheory.Functor.obj` |
| `root.arg[1].arg[6].arg[3].arg[5].arg[0]` | `DerivedCategory.Plus` |
| `root.arg[1].arg[6].arg[3].arg[5].arg[0].arg[2]` | `SheafOfModules.instAbelian` |

The complete raw pair was retained before equality/difference processing. Raw DAGs record structural sharing, constructors, constants/universes, exact fvars and references; the context projection records nineteen original locals and twenty expected-binder mappings.

Actual raw type: `/Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025/migration/implementation/exceptional-producer-type-extraction/pointwise-type-pair/ACTUAL.rawexprdag.txt`.
Expected raw type: `/Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025/migration/implementation/exceptional-producer-type-extraction/pointwise-type-pair/EXPECTED.rawexprdag.txt`.
Context: `/Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025/migration/implementation/exceptional-producer-type-extraction/pointwise-type-pair/ALIGNED_CONTEXT.txt`.
Native stdout: `/Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025/migration/incremental-compiler/diagnostics/r4-pointwise-type-pair-d72be55f/stdout.log` (185578 bytes; SHA256 `4de9de7405d7b1386872b1e450cc88954974b4b53ed1fa88414c9003c875f6f7`).

Executed script SHA256: `b49ec836c5de403db90751ac5ffc883d94e857312442136895c1260fbb10227f`.
Request SHA256: `03f280efce0d4fd148b7cb336c7a146ed6f5eed26c4f03bf8b32bd0f4b8cbe2d`.
Producer source SHA256: `6a84bc472cb2a3b2841d27fdb753e907371fe633c7d0364fd288518b7a31afbf`.
Pointwise source SHA256: `b72088c989598e3e26f361def624f8dc2bd00e8d00b7e2386e6b9ef971f4c827`.
Provider source SHA256: `65bc75bd87f6942ed330fbc8ccfc98bdf61a14989f0b422a98d87f9a64e91ef7`.
Provider artifacts SHA256: `b8a81d3f1d55c994c43b511c84dec652f6367b2ff9a0ad34d1f9a153192e3bf6`.
Setup SHA256: `922034a0e8a01bed3cdcc4a09ed1ab37d1fd5b7f6b15d5a3f26e1c8d58a250f5`.
Lean 4.34.1; mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Exact observed native argv, cwd, receipt, source archive, and all raw data locators are recorded in `/Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025/migration/implementation/exceptional-producer-type-extraction/pointwise-type-pair/RETURN.json`. The controlled current-N source archive is separate from the frozen mathematical provider identity.

Mechanical local reproduction of the projection (no Lean execution):

```sh
python3 "/Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025/migration/implementation/exceptional-producer-type-extraction/pointwise-type-pair/extract_raw_pair.py" \
  "/Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025/migration/incremental-compiler/diagnostics/r4-pointwise-type-pair-d72be55f/stdout.log" \
  "/Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025/migration/implementation/exceptional-producer-type-extraction/pointwise-type-pair"
```

Any native rerun remains with incremental_compile_owner through its existing controlled frozen-candidate runner and unchanged default profile. No further run is requested.

Earlier Prop-definition mode was never sealed or launched. Formation3acb failed on serializer syntax before generating a raw pair; the executed b49 repair changed only that syntax. Neither output nor status has been relabeled across those inputs. The earlier twelve-head result remains a separate historical product.

No Meta.isDefEq, native functor/exchange unfolding, explicit normalization, producer/theorem proof-body inspection, timeout-cause verdict, proof assertion about the pointwise equation, or production repair was performed. The predicate may be exposed by ordinary inferType processing of the actual applied term, as assigned; no custom unfolding step was used.

The finite tooling product has no remaining extraction gap. Interpretation of this pair, definitional equality, timeout causation and any source repair remain with the mathematical author.
