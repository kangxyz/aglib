# Rationality of original stalks above one rational target point

Source: [ModelLocalization.lean](ModelLocalization.lean).

Import `Aglib.AlgebraicGeometry.Surfaces.RationalSingularities.ModelLocalization`.
The namespace is `AlgebraicGeometry.Scheme.RationalSingularities`.

`stalk_isNagata_and_normalModificationH1Vanishing_of_target_stalk` takes an
original proper dominant birational map `g : Y -> X` of integral schemes,
normal `Y`, and an actual point `x` whose original stalk `S` is Nagata of
dimension exactly two and satisfies `NormalModificationH1Vanishing S`.
For an original closed nongeneric `y : Y` with `g y = x`, it derives both
Nagata and the same universal H1-vanishing predicate for `Y.stalk y`.

No global rationality, normality or Noetherianity of `X` is assumed. There
is no separate global Noetherianity or dimension premise on `Y`. Genuine
Nagata of `S` supplies the local Noetherian input. Dimension two is retained
because the existing rationality-propagation theorem requires it.

The proof uses only the LITERAL `pullback g (X.fromSpecStalk x)`. Its native
first projection is dominant and identifies original stalks; properness and
actual surjectivity of `g` make the second projection proper and dominant.
The existing original field-square cancellation derives its birationality.
The actual closed lift of `y` is nongeneric by dominance of the first
projection, not by a new local model or a supplied lifted-point premise.

Original rationality propagation applies to this normal proper birational
model over `S`. The right component of the SAME original stalk-arrow
isomorphism transports its H1 predicate back. The inverse of that same ring
equivalence transports Nagata by its finite algebra structure. No alternative
residue map, scalar field or cohomology object is introduced.

For a normalized chain, taking `g` to be an actual prefix makes this literal
pullback exactly the existing LocalStages model. Closedness and nongenericity
are genuine inputs here; future singular-ancestor geometry must derive them.
Ordinary blowup normality, normalization isomorphisms, canonical generation,
Gorensteinness and resolution existence are not conclusions of this leaf.

Direct consumers: [AlgebraicGeometry/Surfaces/Resolution/NormalizedPointBlowupChain/OrdinaryStages](../Resolution/NormalizedPointBlowupChain/OrdinaryStages.md).
