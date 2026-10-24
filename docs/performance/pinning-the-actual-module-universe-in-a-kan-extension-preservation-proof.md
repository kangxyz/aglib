> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#pinning-the-actual-module-universe-in-a-kan-extension-preservation-proof) · [Context](original-context.md) · [Case index](README.md) · [Previous record](use-the-native-isomorphism-to-monomorphism-constructor-directly.md) · [Next record](keep-native-shift-structures-explicit-in-the-canonical-exchange-proof.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Pinning the actual module universe in a Kan-extension preservation proof

Basis: Lean 4.34.1, Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`,
Aglib private HEAD `2c34f185fa859e862661f939cd216b07bcccfb26`.
This records ordinary author repair, not a benchmark or a compiler-defect claim.

The failed run `remote-a6f5a8f9129a467b96fc8a03d1aadb5c`, source snapshot
`35ac35bf7c7b5e64ad72036331dc00b219fe0d0cf0a9fe9dc970228ae06dd8a5`,
reported a stuck universe constraint at `ZModImages.lean:93:2`:
`u + 1 =?= max (u + 1) ?u`, while synthesizing limits of the actual
`ModuleCat.{u + 1} (ZMod n)`. Earlier explicitly typed functors and comparison
isomorphisms alone had not fixed the unresolved universe of the limit instance.
The mathematical statement and ordinary 200000-heartbeat limit were unchanged.

The successful proof keeps the native comparison
`V.lanCompIsoOfPreserves G.op`, with `V` the actual module-to-abelian forgetful
functor and `G` the actual small-etale site base-change functor. For each finite
shape `J : Type (u + 1)`, it installs the exact native instances

```lean
ModuleCat.hasLimitsOfShape.{u + 1, u + 1, u + 1, 0}
ModuleCat.forget₂AddCommGroup_preservesLimitsOfSize.{u + 1, u + 1, u + 1, 0}
```

and then explicitly constructs preservation for both postcomposition functors
with `whiskeringRight_preservesLimitsOfShape`, fixing the actual source,
target and shape. Reflection of those limits and the original Kan comparison
prove preservation for the module Kan extension. No extra mathematical
premise or alternate inverse image was introduced.

Validated leaf SHA-256:
`a5e16619ecc3507b42737d94be44a13d8ae1418d5de3a42f5a0e0ae0734d27ba`.
The run `remote-0af3ec46961642fe80cacaa0f3f9a10a`, source snapshot
`bbe7c640f9c3b77652f248f6782d497315ba3d870818777bc7b2113af0a95d98`,
compiled this actual leaf successfully in 5.8 seconds. Its same four-frontend
batch also compiled `HigherImageAcyclic` and failed only the two other
dependent leaves `ZModRetract` and `ZModAcyclic`; the overall run status is
**failed**, not a successful closure claim. No additional benchmark, replay
or verification cycle was run for this note.

Exact local evidence:

- `remote-runs/remote-a6f5a8f9129a467b96fc8a03d1aadb5c/build.log`
- `remote-runs/remote-0af3ec46961642fe80cacaa0f3f9a10a/build.log`
- Both runs' accompanying `receipt.json` and `compiler-events.jsonl`.


