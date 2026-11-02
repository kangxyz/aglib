# Replacement retaining the specified proper-model factorization

Source: [FactorReplacement.lean](FactorReplacement.lean).

`exists_stalkReplacement_factor` has the actual global proper target
`b : B → X`, locally Noetherian `X`, closed centre `x`, and an isomorphism
of `b` off that centre. The supplied actual proper stalk model `p` is
isomorphic on the punctured local spectrum. A supplied arrow `a : T → B`
has its original triangle `a ≫ b = p ≫ X.fromSpecStalk x`.

The result constructs a `StalkReplacement` and an actual proper factor
`r : R.Y → B`, retaining BOTH `r ≫ b = R.h` and `R.a ≫ r = a`.
It is not a theorem assuming an algebraization/factorization oracle.

The target finite-presentation model is the literal pullback of `B` to an
original affine neighborhood. Native `Model.exists_map` spreads the given
arrow with its cartesian `Map.isPullback` comparison. Properness of that
arrow follows from source properness and separated target structural map.
It is isomorphic over the overlap because both structural maps are. The
already constructed binary `glueNeighborhood` is then used over `B`, gluing
the factor to the identity off the inverse image of the original centre.
Actual squares paste back to the original local spectrum of `X`.

[FactorNormalization](FactorNormalization.md) applies the original
normality and proper-birational criteria to this constructed factor;
[SupportedChain](SupportedChain.md) uses it in the prescribed-chain induction.

Direct consumers: [AlgebraicGeometry/Descent/LocalModification/FactorNormalization](FactorNormalization.md).
