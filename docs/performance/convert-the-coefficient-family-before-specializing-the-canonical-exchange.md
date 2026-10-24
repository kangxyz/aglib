> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#convert-the-coefficient-family-before-specializing-the-canonical-exchange) · [Context](original-context.md) · [Case index](README.md) · [Previous record](bounded-presentations-preserve-typed-section-transport.md) · [Next record](share-the-actual-coefficient-single-data-head-before-transporting-exchange-tests.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Convert the coefficient family before specializing the canonical exchange

Basis: private Aglib HEAD `2c34f185fa859e862661f939cd216b07bcccfb26`,
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1.
This records existing scoped compilation observations. No benchmark, replay
or additional check was run, and the ordinary budgets were unchanged.

Run `remote-1863ac2989664358a4a7f2d9e15a72bb`, source snapshot
`f05d77f18121237fffa1bace745947db2dd16e8efce3c8ffa64f12266795a271`,
compiled `AllModuleCoefficients` successfully in 9.3 seconds, then rejected
the two concrete bounded-coefficient composition/descent declarations with
**kernel deterministic timeout** diagnostics. `BoundedCoefficients` source
`83b15994453093d37b94c1f82c29b97b4277dce8562d323f5bb0eadc0b92d981`
took 295 seconds according to its actual frontend log. The unknown-constant
errors in its two higher wrappers were cascading consequences.

The failing wrappers converted the hypotheses inline:

```lean
fun J _ => hOuter _ (zmodUnderlying_nsmul_id X n J)
```

This supplied the literal `beta.app (single (underlying J))` test where the
compiled injective reduction used the protected regular `zmodSingle` head.
The effective repair moves that conversion to a typed generic boundary
**before** specializing the original exchange. The bridge takes

```text
single : A -> B, U : M -> A, Z : M -> B,
e : Z = U followed by single,
beta : L -> R, P : A -> Prop,
h : every P-coefficient has invertible beta on its single,
hU : every injective I satisfies P (U I).
```

It substitutes the whole functor equality with variable `beta`, then returns
the injective tests directly at `Z.obj I`. The concrete consumer supplies
the already compiled original `zmodSingle`, its whole original functor
equality by `rfl`, the actual underlying functor, and its actual annihilation
theorem. Both concrete wrappers then pass tests with exactly the same shared
data head as the compiled injective provider.

The public bounded-coefficient signatures are unchanged: they use the
literal original single of the actual abelian coefficient. The canonical
`derivedBaseChangeMap`, every higher-image map, all six independent abelian
derived-category universes, and the actual modulus hypothesis are unchanged.
There is no new mathematical premise, alternate coefficient or exchange.
The bridge preserves the actual original object and arrow formulas through
the existing `zmodSingle_obj` and `zmodSingle_map` identities.

Validated source:
`4d8eb96a1d6e9595c34236da6d95d7aff0fb27ab23c08729715b906ea2393385`.
Run `remote-92dc3e6bec274704977cd8711ecec024`, source snapshot
`044e3e0d4434e59e6509c9ca93d56224055c88aaee1f393e64efe8afdcf4d3ab`,
compiled the complete bounded leaf in 5.5 seconds and its original
all-degree `HigherReduction` consumer in 4.9 seconds. This final run had
exactly two actual frontends, both successful, with exit code zero and
14.42 seconds overall wall time. Earlier matching leaf successes were
reused; the Lake progress index is not a count of fresh frontends.

The comparison records the successful proof boundary, not a performance
ratio or a diagnosis of a Lean defect. Existing logs, receipts and compiler
events remain under the two run IDs in this task's `remote-runs/` directory.


