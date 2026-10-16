# Actual Kahler differentials and canonical pullback

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.Modules.Differentials.Basic`, owns `Scheme.Modules.Differentials`. For an actual field scheme, `differentialPresheaf` is the relative Kahler differential presheaf and `differentialSheaf` its actual module sheafification. `differentialSheafHomEquiv` is the universal derivation interface against an actual module sheaf.

`differentialSheafDerivation`, `differentialPushforwardMap` and `differentialPullbackMap` use the actual structural map and adjunction. The map sends `d(a)` to `d(f# a)` and has genuine hom-extensionality and identity/composition formulas. Smoothness or etaleness is not needed to construct these maps; fields and schemes retain universe `u`.

[EtalePullback](EtalePullback.lean) proves `Scheme.Modules.Differentials.EtalePullback.isIso_differentialPullbackMap` for the actual canonical arrow of an etale field-scheme morphism. `Scheme.Modules.Differentials.etaleDifferentialIso` is `asIso` of that same arrow, and `etaleDifferentialIso_hom` is its exact `rfl` hom equation. No global supplier premise is required.

[SmoothRank](SmoothRank.lean) proves `Scheme.Modules.Differentials.differentialSheaf_hasRank_of_smooth K X n hX` over every field in the source universe and in every smooth relative dimension. Actual standard-smooth affine charts supply the local bases. `Scheme.Modules.Differentials.smoothDifferential_finiteLocallyFree X n hX` consumes that proved rank. The former global theorem-family premises and the empty `Properties` entry are retired. The actual successors are `SmoothRank` and `EtalePullback`.

Lower actual module pullback, structural maps and [rank/class](../LocallyFree/README.md) interfaces feed the maps. General differential consumers use them without a canonical-bundle degree, genus or curve Riemann–Roch assertion.

The minimal direct selection from local Aglib main `40af743` is recorded in
[the migration manifest](../../../../doc/migration/upstream-smooth-differentials.json).
Each selected leaf and the independent public consumer passed at the default
budgets. The standard-smooth basis supports independent ring and algebra
universes. The global rank theorem retains the source universe and includes
the empty scheme. Exterior powers, the canonical line, and its identification
with the Serre dualizing coefficient remain separate proof obligations.
