# Geometric field-extension properties

[Connected](Connected/README.md) treats the actual field-base-change projections and common-overfield maps. Over an algebraically closed field, arbitrary field extension preserves connectedness of an arbitrary connected scheme; connectedness after the chosen algebraic closure detects geometric connectedness over an arbitrary original field.

The connectedness sources extend native Mathlib geometric predicates and pullbacks, preserving field, scheme and universe conditions. These results add no finite type, properness or fixed dimension premise.

[Integral global sections](Integral/GlobalSections.lean) proves
`Scheme.constants_bijective_of_proper_geometricallyIntegral`: the actual structural
constants map of a proper geometrically integral field scheme is bijective. It
requires no module-cohomology finiteness family. The existing
`ProperGeometricallyIntegralConstants` predicate remains defined in its historical
[constants-input owner](../Cohomology/Finiteness/Constants.lean); the direct theorem
is now an actual supplier.
