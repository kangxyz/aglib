# Actual ideals of height-one integral closed subschemes on regular surfaces

[RegularSurface.lean](RegularSurface.lean) retains the public theorem
`Scheme.Hom.idealModule_isLocallyRankOne_of_regularSurface` with the same
hypotheses and conclusion:

- `X` is locally Noetherian;
- `C` is integral and `i : C ⟶ X` is an actual closed immersion;
- every actual `X.presheaf.stalk x` is regular local of Krull dimension at most
  two;
- every actual `RingHom.ker (i.stalkMap c).hom` has height one.

The conclusion is `IsLocallyRankOne X (Scheme.Hom.idealModule i)` for the actual
kernel of the structure-module map and its canonical `idealInclusion i`.

Integrality of `C` makes each source stalk a domain, so each actual stalk-map
kernel is prime. The accepted height-one basis supplier in
[HeightOnePrincipal](../../../RingTheory/RegularLocalRing/HeightOnePrincipal.lean)
then gives a singleton basis of each actual kernel over its actual ambient
stalk. These bases feed
`Scheme.Hom.idealModule_isLocallyRankOne_of_stalkKernelBasis` in
[StalkKernel](StalkKernel.lean).

The shared criterion owns the canonical germ/kernel comparison,
finite-presentation basis spreading, outside-image unit ideal, and actual
spectral and restriction maps. The surface result contains no duplicate gluing
implementation. Its dimension bound and height-one premise remain explicit.
