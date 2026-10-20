# Geometric field-extension properties

[Regular](Regular.lean) defines `GeometricallyRegular f` by regularity of all
actual stalks after every field base change. It proves stability under base
change and restriction to a source open, and equivalence with the same property
on every residue-field fiber. Flatness is a separate condition. For a locally
finite-type morphism, these field base changes are locally Noetherian, so this
stalk formulation gives the usual geometric regularity of the fibers. Its
consumer is the [smoothness criterion](../Morphisms/Smooth/GeometricRegularity.lean).

[Connected](Connected/README.md) treats the actual field-base-change projections and common-overfield maps. Over an algebraically closed field, arbitrary field extension preserves connectedness of an arbitrary connected scheme; connectedness after the chosen algebraic closure detects geometric connectedness over an arbitrary original field.

The connectedness sources extend native Mathlib geometric predicates and pullbacks, preserving field, scheme and universe conditions. These results add no finite type, properness or fixed dimension premise.

[Integral global sections](Integral/GlobalSections.lean) proves
`Scheme.constants_bijective_of_proper_geometricallyIntegral`: the actual structural
constants map of a proper geometrically integral field scheme is bijective. It
requires no module-cohomology finiteness family. The existing
`ProperGeometricallyIntegralConstants` predicate remains defined in its historical
[constants-input owner](../Cohomology/Finiteness/Constants.lean); the direct theorem
is now an actual supplier.

`SmoothCurve` supplies `Scheme.isDomain_stalk_of_smoothOfRelativeDimension_one`,
`isIntegral_of_connected_of_smoothOfRelativeDimension_one` and
`geometricallyIntegral_of_smoothOfRelativeDimension_one_of_geometricallyConnected`.
Smooth relative dimension one over an arbitrary field gives domain stalks;
connectedness then gives integrality. Geometric connectedness gives geometric
integrality after arbitrary field base change. Properness, perfectness and
characteristic restrictions are absent. The rational-point cotangent supplier
is [RationalPoint/SmoothCurve](../RationalPoint/SmoothCurve.lean);
principal-maximal-ideal algebra reuses the existing native `IsLocalRing` provider.
