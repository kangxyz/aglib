# Actual Kahler differentials and canonical pullback

[Basic](Basic.lean), imported as `Aglib.AlgebraicGeometry.Modules.Differentials.Basic`, owns `Scheme.Modules.Differentials`. For an actual field scheme, `differentialPresheaf` is the relative Kahler differential presheaf and `differentialSheaf` its actual module sheafification. `differentialSheafHomEquiv` is the universal derivation interface against an actual module sheaf.

`differentialSheafDerivation`, `differentialPushforwardMap` and `differentialPullbackMap` use the actual structural map and adjunction. The map sends `d(a)` to `d(f# a)` and has genuine hom-extensionality and identity/composition formulas. Smoothness or etaleness is not needed to construct these maps; fields and schemes retain universe `u`.

[EtalePullback](EtalePullback.lean) supplies `Scheme.Modules.Differentials.EtalePullback.etaleDifferentialPullback`: an actual etale field-scheme morphism makes this canonical map invertible. The supplied `etaleDifferentialIso` has the same map as its forward arrow.

[Properties](Properties.lean) retains `SmoothDifferentialRank` as an explicit all-field/all-dimension input. `smoothDifferential_finiteLocallyFree` takes that family as `hstandard` and concludes finite local freeness of the actual differential sheaf for a smooth field scheme of relative dimension `n`. The differential construction itself does not supply this rank theorem.

Lower actual module pullback, structural maps and [rank/class](../LocallyFree/README.md) interfaces feed the maps. General differential consumers use them without a canonical-bundle degree, genus or curve Riemann–Roch assertion.
