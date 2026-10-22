# Weak transforms in saturated charts

`WeakTransform.lean` belongs to `Localization.Away` and uses the actual
`saturatedChart A I a` inside `Localization.Away a`. Its construction is

`weakTransform I J a r = (J.map algebraMap).colon {algebraMap a ^ r}`.

`map_center_eq_span` proves that the actual centre ideal extends to the
principal exceptional ideal when `a ∈ I`. If `J ≤ I ^ r`,
`exceptional_pow_mul_weakTransform` proves the ideal equality
`(algebraMap a ^ r) * weakTransform I J a r = J.map algebraMap`.
The exceptional power acts injectively in the chart because its image is a
unit in the ambient localization. The factor ideal is therefore unique.
These statements require only a commutative ring, not a domain or regularity.

`exceptional_pow_mem_weakTransform` puts the exceptional power `N-r` in the
transform from `I ^ N ≤ J` and `r ≤ N`. This supplies the annihilating power
needed for the exceptional support calculation. It alone does not prove that
support is finite.

`map_exceptional_pow_mul_weakTransform` carries the factorization through any
ring map from the chart. `map_weakTransform_eq_colon` further identifies the
extended transform with the target colon ideal when the image of the
exceptional parameter is regular. This is the algebraic interface for the
actual exceptional-point localizations.

For surface principalization, take `I` to be the actual maximal ideal of a
two-dimensional regular local ring and `r` to be the actual order of `J`.
This module accepts the exponent and proves the displayed division. It does
not select that order or prove finite support, a colength inequality, finite
principalization, or common regular domination. The literal chart and residue
coordinates are supplied separately by `RegularPair.lean` and
`RegularPair/Reciprocal.lean`.
