# The original residue-field scalar tower

Source: [ResidueTranscendence.lean](ResidueTranscendence.lean).

For locally finite-type `f : X ⟶ Y` and a closed `x : X`,
`residueFieldMap_finite_of_closedPoint` gives finiteness of the original
`f.residueFieldMap x`. Its implementation is the lower
`Scheme.Hom.residueFieldMap_finite_of_closedPoint` in
`Morphisms.FiniteType.ResidueField`; this surface interface is a thin caller.

For composable `f : X ⟶ Y`, `g : Y ⟶ Z`, if
`κ(g(f(x))) → κ(f(x))` is finite, then an element of `κ(x)`
transcendental over the first field through the composite map is
transcendental over the intermediate field through `f.residueFieldMap`.
`transcendental_residueFieldMap_of_finite` proves this using the scalar tower
from `residueFieldMap_comp`.
`transcendental_residueFieldMap_of_closedPoint` derives the finite extension
when `g` is locally of finite type and `f x` is closed.

The fields and all three scalar actions are those of the original maps.

Present consumers: [CurveSurvival](CurveSurvival.md), [Resolution/RationalDoublePoint/PrefixResidue](../../Resolution/RationalDoublePoint/PrefixResidue.md).
