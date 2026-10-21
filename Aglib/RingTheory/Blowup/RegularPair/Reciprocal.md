# Original reciprocal chart coordinates

`Localization.Away.pairReciprocal a b` is the actual algebra homomorphism

```text
A[U]/(b U - a) → (A[T]/(a T - b))[1/T],   U ↦ T⁻¹.
```

The relation is proved from `b = a T` in the original quotient and the
distinguished inverse in its actual localization. It requires only a
commutative base ring. `pairReciprocal_coordinate` fixes the forward coordinate
equation; the algebra-homomorphism structure retains the original base map.

`pairChartFibreEquiv_coordinate` records that the previously proved saturated
fibre comparison sends the class of the original ratio coordinate to `X`.
This second statement retains the two explicit regular-pair hypotheses of
`pairChartEquiv` and does not assume an overlap or exceptional-fibre model.

The consumer is `AlgebraicGeometry/Blowup/RegularPoint/Charts`. These ring maps
alone do not supply the global projective-line or normal-line identification.
