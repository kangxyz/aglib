# Regular finite hyperplanes on the full coefficient curve

Source: [Hyperplane.lean](Hyperplane.lean).

This leaf constructs a regular finite hyperplane through an actual rational
point. The curve may be nonreduced. The intermediate explicitly retains an
infinite field; arbitrary-field extension and descent remain separate consumers.

## Endpoint and hypotheses

`exists_regular_finite_hyperplane_through_rationalPoint` takes:

* a field `k` with `Infinite k` and a finite coordinate type `ι`;
* the original closed immersion `j : C → ProjectiveSpace k ι`;
* at each **closed** point of `C`, a regular nonunit in its original stalk whose
  principal ideal has maximal-ideal radical;
* an actual rational point `r : Spec k → C` with
  `r ≫ j ≫ ProjectiveSpace.toSpec = id`.

It returns a genuine finitely supported coefficient vector `c`, monicity of the
original pulled polynomial section and its original contraction, finiteness of
that contraction's original zero scheme, and an actual lift of `r` into that
same zero scheme. No associated-point, incidence, regular-section existence,
finite-divisor, reducedness, smoothness, perfectness, or genus-zero premise is
inserted.

## Original maps

`curveHyperplaneLine` is the actual geometric pullback of the original
projective twist. `curveHyperplaneSection` is the pullback of the original
`twistingMultiplyGlobal`, using only native zero-twist and pullback-unit
isomorphisms. `curveHyperplaneIdealMap` is its original `sectionContraction`.
The zero scheme and inclusion are native `Hom.zeroScheme` and
`Hom.zeroInclusion` of this same map.

The coefficient-map square
`closedProjectionFormula_unit_coefficient_square` explicitly retains the
original closed projection formula. `coordinateRingEquivSections_Spec_map`,
`coordinateSectionEvaluate_fromSpec`, and
`primeIdealOf_rationalPoint_eq_kernel` identify the original chart morphism and
prime. `rationalPoint_appLE_eq_evaluate` identifies the original restriction
map with evaluation followed by `ΓSpecIso.inv`.

The native pulled-cocycle coefficient formula gives literal pullback-zero of
the same polynomial section. Native pullback-composition and tensor naturality
transport this to the original curve section and contraction. Its actual
kernel ideal then supplies the native closed-immersion lift of the original
point into the original zero scheme.

## Proof suppliers

Association is first transferred through the original surjective affine chart
map `A → B`. The ambient module is **`j_*O_C`**, not the ambient structure ring.
The original curve-stalk parameter and actual affine stalk localization exclude
its corresponding associated prime. The passed constrained-hyperplane theorem
then supplies the section.

The closed projection formula transports monicity to the actual geometric
pullback. Tensoring by the actual inverse line gives monicity of the original
contraction. The actual invertible ideal locally has a regular generator;
`quotient_isArtinianRing_of_regular_kernel_element` proves dimension drop.
The full dimension bound is derived from the closed parameters by
`Scheme.dimension_le_one_of_closed_parameters`. The resulting locally Artinian
zero scheme has discrete fibers; properness and finite type imply finiteness.

The Cartier argument reuses the generic portion of
`EffectiveCartierDivisor/Smooth/Field.lean`, replacing its smoothness-derived
dimension estimate with the original closed-parameter estimate.

Coefficient-canonical quotient generation, its numerical dimension estimate,
and arbitrary-field descent are separate the coefficient-generation argument consumers and are not claimed
complete by this hyperplane endpoint.

The original `curveHyperplaneDualIdealIso` is now owned here, shared by
canonical generation and the anticanonical Hilbert base-change consumer.
Its single unchanged body uses the native zero-ideal line-bundle isomorphism,
bidual map and internal-Hom comparison.

Direct consumers: [AlgebraicGeometry/Cohomology/Duality/Projective/Relative/CohenMacaulayCurve/AnticanonicalHilbert/Geometric](../AnticanonicalHilbert/Geometric.md).
