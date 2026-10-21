# Arithmetic genus of every Weierstrass cubic

`Genus.lean` computes cohomology of the same homogeneous-quotient `Proj` as
`Projective.lean`. `curveOverH1Equiv` has target the original coefficient
field and source the existing `Scheme.coherentH1`, with its actual
structural scalar action. `curveOver_coherentGenus` states arithmetic genus
one for every Weierstrass equation over every field. Smoothness and a
nonzero discriminant are unnecessary for this calculation.

The actual ring bases, overlap quotient, and homogeneous-localization
comparisons belong to the lower [Genus/Charts](Genus/Charts.md) provider.
`Genus.lean` supplies their structural-field section comparisons and the
cohomological conclusion.

The affine chart has the alternative monic presentation

```text
R[y][x] / (x³ + a₂x² + (a₄ - a₁y)x + a₆ - a₃y - y²).
```

`affineCubicEquiv` identifies this presentation with Mathlib's original
affine coordinate ring, retaining both coordinates and the coefficient
map. The monic power basis is `1,x,x²` over `R[y]`. The existing infinity
chart has basis `1,u,u²` over `R[v]`, where `u=X/Y` and `v=Z/Y`.

The actual overlap is `infinityOverlapRing W`, the localization of that
infinity ring at `v`. Its Laurent basis is `uⁱvʲ`, for `i : Fin 3` and
`j : ℤ`. The original chart maps send

```text
yⁿxⁱ ↦ uⁱv^(-i-n),       vⁿuⁱ ↦ uⁱvⁿ.
```

These two images span every overlap basis vector except `u²/v`.
`overlapChartSubmodule` is the sum of their actual linear-map ranges.
`overlapChartQuotientEquiv` identifies its quotient with `R`; its forward
map takes the coefficient of `u²/v`. This algebraic calculation works over
every nontrivial commutative ring.

`homogeneousOverlapEquiv` identifies that localization with the native
homogeneous localization at `YZ`. Its affine restriction comparison
retains the literal maps `x=u/v` and `y=1/v`. Mathlib's canonical
`Proj.basicOpenIsoAway` maps and `awayMap_awayToSection` identify these
maps with the actual structure-sheaf restrictions on `D₊Y` and `D₊Z`.
`basicOpen_constantSection` checks the original structural constants;
the section comparisons are therefore linear for the same field action.

The general
[structural first-cohomology comparison](../../Cohomology/MayerVietoris/StructuralFirstCohomology.lean)
identifies native H¹ with this section cokernel. The monic bases and
localization maps specify the quotient calculation; no replacement
elliptic curve, representability premise, or cohomological finiteness
supplier is assumed.
