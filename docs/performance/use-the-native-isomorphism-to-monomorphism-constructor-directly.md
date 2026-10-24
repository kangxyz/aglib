> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#use-the-native-isomorphism-to-monomorphism-constructor-directly) · [Context](original-context.md) · [Case index](README.md) · [Previous record](share-the-actual-coefficient-single-data-head-before-transporting-exchange-tests.md) · [Next record](pinning-the-actual-module-universe-in-a-kan-extension-preservation-proof.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Use the native isomorphism-to-monomorphism constructor directly

Basis: private Aglib HEAD `2c34f185fa859e862661f939cd216b07bcccfb26`,
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1.

The generic `Plus.InjectiveComparison.homology_mono_successor` uses an actual
injective presentation and its actual cokernel. In the failed run
`remote-ceb0c3469fbd493a9444108bdba76e26`, package
`d874a1584ea2cb92369a63b6786e192c0667cd3c8a62f8730ee1e800c3fe1cfb`,
source `5f07c5e041f5c4a19a393b1a23c4531155bd081f653bab01ee1837eeec376a26`,
the already available preceding-degree isomorphism hypothesis was installed
locally. A subsequent `infer_instance` for monicity of precisely that
homology-comparison arrow exhausted the native 20000 typeclass heartbeats.
The diagnostic was at line 131, on the actual cokernel of the chosen
injective presentation. This was not a kernel timeout or an OOM.

The effective repair changes only that final instance search:

```lean
have := hPrev (cokernel P.f)
exact IsIso.mono_of_iso _
```

The existing native constructor consumes the same local isomorphism proof
and yields monicity of the same original arrow. No extra mathematical
premise, altered cokernel, comparison map or search-budget override is used.
This records the validated proof boundary, not a diagnosis of why the wider
instance search visited its particular alternatives.

Successful source:
`7e54af9098fc49f2b09564e30facada627d7ab8b4a05c89d0c460e8c1cd7fc6f`.
Actual run `remote-513fd164d7b74707b30c0616780ee6cb`, package
`fdd10aa46960815795782d7e809e939a2bd275f674631b5faf2818e97276c14e`,
compiled this leaf in 12 seconds. The three-frontend scoped batch passed all
three selected leaves; its other two were `GeometryCriterion` and
`SingleHigher`. The enclosing run succeeded. No replay, benchmark, lint or
extra check was run to prepare this note; the ordinary 200000-heartbeat
declaration limit and 20000 typeclass limit were retained.

Evidence is in the two runs' existing `build.log`, `receipt.json` and
`compiler-events.jsonl` under this task's `remote-runs/` directory.


