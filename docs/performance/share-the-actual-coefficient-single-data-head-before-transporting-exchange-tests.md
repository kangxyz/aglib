> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#share-the-actual-coefficient-single-data-head-before-transporting-exchange-tests) · [Context](original-context.md) · [Case index](README.md) · [Previous record](convert-the-coefficient-family-before-specializing-the-canonical-exchange.md) · [Next record](use-the-native-isomorphism-to-monomorphism-constructor-directly.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Share the actual coefficient-single data head before transporting exchange tests

Basis: private Aglib HEAD `2c34f185fa859e862661f939cd216b07bcccfb26`,
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1.
These are ordinary scoped compilation observations, not benchmark runs or a
compiler-defect diagnosis. The standard 200000 declaration-heartbeat limit
was retained throughout.

The original `InjectiveExchange` assembled canonical vertical-pasting,
acyclic-single comparisons and actual coefficient retracts directly at the
expanded original `singleFunctor.obj (zmodUnderlying.obj I)` terms. Run
`remote-b72d18ebd6954922a783d46bbfa25a12` failed both concrete reduction
theorems with **kernel deterministic timeout** diagnostics. Its leaf source
was `a78dbd5ed97cfc826a9acd1209c29fc475dcab92bef7261cb1b3006742ab846d`;
the log reports 280 seconds for that frontend. The later unknown-constant
diagnostic was a consequence of the rejected descent declaration.

Extracting only the logical transport into generic `NatTrans` injective-test
lemmas was insufficient. In `remote-ceb0c3469fbd493a9444108bdba76e26`, package
`d874a1584ea2cb92369a63b6786e192c0667cd3c8a62f8730ee1e800c3fe1cfb`,
leaf source `dc58e249c88670ef11a799230886b18d907c1cadb7fa455e2f8a373664277142`
again failed both concrete wrappers with kernel deterministic timeouts. The
log reports 247 seconds for this frontend. No accepted theorem or broader
scope is inferred from either failed invocation.

The effective repair gives the actual coefficient embedding one shared
regular data head:

```lean
def zmodSingle (X : Scheme.{u})
    [HasDerivedCategory.{dX} (AbelianSheaf.{u,u+1} X)] (n : ℕ) :
    ZModSheaf X n ⥤ DerivedCategory.Plus (AbelianSheaf.{u,u+1} X) :=
  zmodUnderlying X n ⋙
    DerivedCategory.Plus.singleFunctor (AbelianSheaf.{u,u+1} X) 0
```

The exposed `zmodSingle_obj` and `zmodSingle_map` formulas are `rfl` and
retain exactly the original object and coefficient arrow. A separately
typed `zmodInjectiveImageSingleIso` returns the previously compiled native
`derivedDirectImageZModInjectiveSingleIso` at these same shared heads. It is
the original acyclic-single comparison from the original right-derived unit.
The generic injective-test composition/descent proofs and the concrete
theorem statements use this identical functor head. The canonical
`derivedBaseChangeMap`, native vertical-pasting and genuine coefficient
retract suppliers are unchanged. No new mathematical premise, alternate
exchange, or injectivity-after-forgetting claim is introduced.

The source interface is normalized to use the shared actual functor; an
unused draft higher-injective wrapper was omitted. The direct original
all-degree reduction consumers remain in the separate upper leaves. No
additional fully expanded certificate was pursued merely to reproduce the
failed conversion.

Validated leaf source:
`e0bf719ae8240bbb4c652648cc7d84cdcd91b2d2c0a05e6de3aab2c5751f24fe`.
Run `remote-5343d4769a9c40948d7108ee21f8548d`, source snapshot
`b8e6140d19600b44c67df20b2b06ce171dc61349e620227ac4396e464a52d849`,
compiled the complete `InjectiveExchange` leaf successfully in 5.4 seconds.
Its two-frontend batch **failed overall**, because the independent
`ExchangeShift` leaf had four ordinary elaboration errors. That run is not
a successful whole-family or proper-base-change closure claim.

The pre-execution snapshot-guard stop reported as invocation `70101` did
not execute a compiler and is not additional proof-failure evidence.

All cited logs and receipts are the existing artifacts under this task's
`remote-runs/` directory. No benchmark, replay, lint or additional build was
run to prepare this note.


