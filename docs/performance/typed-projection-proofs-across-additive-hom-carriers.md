> Preserved original record. [Original source](https://github.com/kangxyz/aglib/blob/d578d2cb686c84187b76dc5f51a2de4b3a41df63/docs/PERFORMANCE.md#typed-projection-proofs-across-additive-hom-carriers) · [Context](original-context.md) · [Case index](README.md) · [Previous record](small-étale-morphism-property-boundaries-preserve-typed-native-objects.md) · [Next record](short-complex-colimit-comparisons-normalize-abstract-endpoints-first.md).
> Commands and status describe the recorded source; [current practice](../PERFORMANCE.md#repair-workflow) remains with the operating guides.

## Typed projection proofs across additive Hom carriers

Evidence: the native FiniteFreeHom target failed in graphs 029 and 034, then passed in graph 036 (5.3 seconds). No additional benchmark was run.

When an additive equivalence on a raw Hom type is converted with `AddEquiv.toAddCommGrpIso`, downstream goals may present its source as the native preadditive Coyoneda `MShrink` carrier and its target as the concrete product cone point. These are definitionally compatible at full transparency but rewriting can reject the entire target as ill-typed at implicit transparency.

Do not repeatedly change equivalent projection rewrite lemmas. After the ordinary associativity and `Pi.isoLimit_hom_π` steps, compose the fully typed canonical projection equality using `congrArg`, not a further rewrite through the additive equivalence. Annotate BOTH objects of `toAddCommGrpIso` explicitly as `AddCommGrpCat.of ...`: otherwise a lambda elaboration leaves the source group as a metavariable (graph 034).

The successful proof uses `exact congrArg (fun f => (E.toAddCommGrpIso : AddCommGrpCat.of X ≅ AddCommGrpCat.of Y).hom ≫ f) (limit.conePointUniqueUpToIso_hom_comp hc j)`, with actual E, X, Y, hc and j supplied. The final generator evaluation is definitional. Keep any required existing backward-defeq options local to the theorem. This is a typed-term elaboration repair, not a reason to increase resource limits or run kernel replay.

