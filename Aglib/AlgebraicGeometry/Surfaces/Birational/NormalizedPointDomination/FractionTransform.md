# Exceptional division of the retained fraction

Source: [FractionTransform.lean](FractionTransform.lean).

`retained_fraction_division` uses integral locally Noetherian schemes
`Z,Y` with integrally closed stalks, a codimension-one point `x : Z`,
and an original square `f ≫ q = p ≫ r`.
The point `f x` has stalk dimension one and `f.stalkMap x` is an isomorphism.

The retained data are a stalk element `u`, target elements `a,b` with nonzero
images, and `u * q.stalkMap b = q.stalkMap a`. Given simultaneous
factorizations of those elements by a nonunit `d` after the native
stalk congruence from the square, the theorem proves that both transformed
images are nonzero, preserve the pulled-back fraction equation, and have
strictly smaller finite DVR order.

The nonzero numerator forces the exceptional image nonzero; locality
preserves its nonunit property. `ExceptionalGenerator` constructs the
factorizations used by `SelectedStep`.

Present consumers: [SelectedStep](SelectedStep.md).
