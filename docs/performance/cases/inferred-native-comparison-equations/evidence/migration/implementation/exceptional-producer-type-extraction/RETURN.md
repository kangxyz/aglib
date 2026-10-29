# Producer type extraction

Actual native run `remote-02ab729d50fb4379ad8dbf878d5f39de` completed with exit 0 in 5.224s, one frontend, unchanged frozen65bc/setup922/default resources. The twelve stored functor arguments are literal applications of the named native constants. None has a raw Functor.mk, lambda, or projection head.

Producer: 19 outer binders, 1584 cached raw subexpressions. Cube: `CategoryTheory.HorizontalMateCubeEquation`, 34 arguments, 1024 cached raw subexpressions; functor slots occupy indices 16–27.

| Slot | Actual constant head (EtaleCohomology prefix omitted) | Universes | Args | Nodes | Full comparison |
|---|---|---|---:|---:|---|
| R₁ | Coefficients.moduleDerivedDirectImage | u, wMS, wMX | 7 | 15 | builder gap |
| R₂ | Coefficients.moduleDerivedDirectImage | u, wMS', wMX' | 7 | 15 | builder gap |
| R₁' | derivedDirectImage | u, wAX, wAS | 5 | 11 | raw structural match |
| R₂' | derivedDirectImage | u, wAX', wAS' | 5 | 11 | raw structural match |
| G | Coefficients.moduleDerivedInverseImage | u, wMS, wMS' | 7 | 15 | builder gap |
| H | Coefficients.moduleDerivedInverseImage | u, wMX, wMX' | 7 | 15 | builder gap |
| G' | derivedInverseImage | u, wAS', wAS | 5 | 11 | raw structural match |
| H' | derivedInverseImage | u, wAX', wAX | 5 | 11 | raw structural match |
| QA | Coefficients.moduleDerivedUnderlying | u, wMS, wAS | 5 | 11 | builder gap |
| QB | Coefficients.moduleDerivedUnderlying | u, wMX, wAX | 5 | 11 | builder gap |
| QC | Coefficients.moduleDerivedUnderlying | u, wMS', wAS' | 5 | 11 | builder gap |
| QD | Coefficients.moduleDerivedUnderlying | u, wMX', wAX' | 5 | 11 | builder gap |

The four Ab slots have full raw alpha/structural equality. For the eight module slots the optional comparison builder stopped before two trailing HasDerivedCategory arguments (actual 7 versus builder 5 arguments, or underlying 5 versus 3). Its false flags do not compare fully constructed intended functors. No difference of native functor heads was observed.

Node counts use cached Expr.forEach, hence unique raw subexpressions under Expr BEq, not expanded tree sizes. Raw alpha equality ignores binder annotations; structural equality uses Expr.equal. Neither invokes Meta definitional equality.

The extractor accesses getConstInfo.type, syntactically peels outer forallE binders, and inspects raw application arguments using the cube declaration binder names. It does not access the producer proof body, unfold the final cube predicate, normalize the original Ab exchange, or claim a reduction/timeout cause. No N/M/provider/production source was changed.

Executed script SHA256: `96e8ac18a0c2b244f7e553a15f037de4e03a28f4fa452dd443d13c3db10fee59`.
Executed request SHA256: `8eba01b93961007ca5367764082b86f29fb678d69bd9d8316d8d14d68cd09abc`.
Producer source SHA256: `6a84bc472cb2a3b2841d27fdb753e907371fe633c7d0364fd288518b7a31afbf`.
Provider source SHA256: `65bc75bd87f6942ed330fbc8ccfc98bdf61a14989f0b422a98d87f9a64e91ef7`.
Setup SHA256: `922034a0e8a01bed3cdcc4a09ed1ab37d1fd5b7f6b15d5a3f26e1c8d58a250f5`.
Provider artifacts SHA256: `b8a81d3f1d55c994c43b511c84dec652f6367b2ff9a0ad34d1f9a153192e3bf6`.
Lean 4.34.1; mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`.

Raw stdout: `/Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025/migration/incremental-compiler/diagnostics/r4-producer-type-extraction-02ab729d/stdout.log` (SHA256 `f0802eab100a6184740725120ed3e7b85b7687270b3ab29b70488affad58e975`, 33297 bytes).
Exact native argv, cwd, receipt, input identities, prior failed attempts, and staged-unexecuted revision are recorded in `/Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025/migration/implementation/exceptional-producer-type-extraction/RETURN.json`.
Native result record: `/Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025/migration/incremental-compiler/diagnostics/r4-producer-type-extraction-02ab729d/result.json`.
Native receipt: `/Users/kang/Documents/New project/tmp/work/etale-abstract-core-research-20261025/foundations/remote-runs/remote-02ab729d50fb4379ad8dbf878d5f39de/receipt.json`.

Reproduction is through incremental_compile_owner only: submit the saved executed candidate bytes/hash to the existing `r4-frozen-candidate-diagnostic.py` wrapper under the controlled `r5tools lean remote ... phase --jobs 2 --threads 4 --lean-memory-mib 12800 --rss-limit-mib 32768` mechanism, with the unchanged setup922. Exact observed native argv is in RETURN.json. No direct runtime or new run is requested.

The primary ProducerTypeExtraction.lean and REQUEST.json have been restored byte-for-byte to the executed 96e8/8eba inputs. The later fcd8 revision is preserved separately as staged and unexecuted. Earlier ffdb and b513 failures remain distinct evidence on their actual script hashes.

Remaining gap: optional full module-slot comparison only. Mathematical interpretation, production repair, and any semantic conclusion remain with the mathematical author.
