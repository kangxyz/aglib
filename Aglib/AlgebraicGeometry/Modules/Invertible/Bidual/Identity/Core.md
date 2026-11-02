# Identity laws of the original bidual map

Source: [Core.lean](Core.lean).

`doubleDualMap_id` proves the identity equation for the original
`doubleDualMap` on arbitrary module sheaves.
It applies the existing internal-Hom identity law twice with the same
structure-unit coefficient.

`doubleDualMap_map_refl` retains an arbitrary original functor and its
native identity law before applying that same bidual map.
There is no quasicoherence, finiteness, regularity or line-bundle
hypothesis. The constructor remains in `Bidual.Map`, and composition
and extension naturality remain in `Bidual.Naturality`.

Direct consumers: [AlgebraicGeometry/Modules/Differentials/Relative/ExteriorCoefficientCoherence](../../../Differentials/Relative/ExteriorCoefficientCoherence.md).
