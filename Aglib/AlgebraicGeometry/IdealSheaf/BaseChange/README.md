# Canonical base change of actual ideal modules

[Map](Map.lean), imported as `Aglib.AlgebraicGeometry.IdealSheaf.BaseChange.Map`, constructs `Scheme.Hom.idealPullbackMap` from the actual kernel universal property and pullback/pushforward adjunction for every displayed commutative square. Its inclusion equation, composition and congruence laws require no flatness or cartesian-square hypothesis.

[Affine](Affine.lean) identifies that specified map with sheafification of the actual scalar-extended ring-kernel map, including its unit and inclusion equations. The affine adjunction comparison directions are part of this interface. [Isomorphism](Isomorphism.lean) treats isomorphism squares with arbitrary vertical maps.

[Flat](Flat.lean) supplies `Scheme.Hom.flatQuotient_idealPullbackMap_isIso`. Its two actual cartesian squares, `IsClosedImmersion i` and `Flat (i ≫ p)` imply invertibility of the specified ideal map. Neither the ambient family nor the base-change morphism needs to be flat; an invertible ideal is also not a premise of this root. The source Cartier specialization retains its original extra rank-one hypothesis as a pointwise corollary.

[Fibre](Fibre.lean) constructs the actual fibre inclusion and cartesian square. Its conditional ideal isomorphism and line-bundle construction retain the explicitly displayed pointwise base-change supplier, closed-immersion, quotient-flatness and rank-one inputs from the source. These conditional interfaces are supplied by the proved `Flat` root in their final consumers; they are not new global theorem-family predicates.

[OpenImmersion](OpenImmersion.lean) proves `Scheme.Hom.idealPullbackMap_isIso_of_isOpenImmersion`: along a cartesian square whose base-change morphism is an open immersion, the canonical ideal map is an isomorphism, with no flatness or closed-immersion hypothesis.

[FlatMorphism](FlatMorphism.md) proves
`Scheme.Hom.idealPullbackMap_isIso_of_flat` for a cartesian square with affine
vertical map and flat base morphism, on arbitrary schemes. It concerns the
same original canonical map and inclusion equation. Its flatness hypothesis
is on the base morphism; the separate `Flat` theorem above instead uses
flatness of the quotient family. The actual [DVR-fibre construction](../Cartier/DVRFibre.md)
uses this flat-base result.
