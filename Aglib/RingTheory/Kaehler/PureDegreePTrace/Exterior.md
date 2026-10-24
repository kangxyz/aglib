# The degree-p trace on exterior differential forms

The source is the actual positive-degree exterior power of
`KaehlerDifferential Λ S`, with the original monogenic presentation
`h : IsAdjoinRootMonic S (X ^ p - C a)`. The map first takes the alternating
insertion component of the proved differential decomposition, wedges the
relation differential in the last position, and applies the existing
`pureDegreePCoeff h` to its tensor coefficient.

For n ≥ 0, its original-wedge formula is

```text
eta wedge z^i dz ↦ 0                  when i < p-1,
eta wedge z^(p-1) dz ↦ eta wedge da.
```

The entire actual map `S ⊗[R] ⋀[R]^(n+1) Ω[R/Λ] → ⋀[S]^(n+1) Ω[S/Λ]` is
annihilated. The formulas determine the map uniquely. Degree one recovers
the original one-form trace under the native `oneEquiv` maps.

Coordinate independence and scalar change are proved through the actual
Kähler exterior map `mapExterior`. Localization identifies the map with
`IsLocalizedModule.mapExtendScalars`; its required module-localization
instances are proved using the exterior base-change supplier. No compatibility
premise or substitute differential carrier is supplied.

The construction uses `CharP R p`. The power-basis and coordinate/scalar
results retain `Fact p.Prime`. Scalar change is over the displayed fixed
Λ and explicitly retains `CharP R' p` on the new coefficient ring.
This includes the nonzero domain localizations used in the height-one
application. No source smoothness, separable residue field, perfect field,
or finite p-rank assumption is made.

The mathematical normalization is Stacks
[0AX5](https://stacks.math.columbia.edu/tag/0AX5).
[Monogenic](../../DiscreteValuationRing/PureDegreeP/Monogenic.md) supplies
actual finite pure degree-p DVR presentations under its stated hypotheses.
Coherent/reflexive scheme assembly remains separate. This module does not
prove canonical-module compatibility or the pure degree-p H1 bound.
