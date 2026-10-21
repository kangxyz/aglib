# Coordinate addition and a given pointed group law

[GroupCompatibility.lean](GroupCompatibility.lean) supplies
`coordinatePointGroupCompatibility` and
`coordinatePointExtensionGroupCompatibility` at the exact original types in
[CoordinateGroup.lean](CoordinateGroup.lean). The inputs retain nonzero
discriminant, the stated characteristic-zero condition, and any actual
`PointedGroupLaw` on the literal original cubic and infinity section.

The proof identifies the restricted ideal of each finite coordinate point
with the native `XYIdeal`; the origin ideal restricts to the unit sheaf.
The actual affine Picard and class-group equivalences turn the native Abel
class into the negative of Mathlib's injective point-class homomorphism.
The given group's multiplication is additive on those Abel classes, using
the actual genus-one supplier.

For an arbitrary field map `k →+* K`, the categorical pullback of that given
group is compared with the literal coefficient model. The multiplicative
point-fibre equivalence returns to the original k-group evaluated at
`Spec K`. Explicit coordinate naturality and a faithfully flat field-extension
test give the original universal extension statement.
