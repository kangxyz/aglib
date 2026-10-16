# Original right-derived descents and shifts

[RightDerivedCommShift](RightDerivedCommShift.lean) proves
`Functor.commShift_of_rightDerived_fac`: the original defining unit square
of a comparison detects its compatibility with shifts. The native localization,
right-derived functor and supplied shift structures are retained, with separate
category and morphism universes and an arbitrary additive shift group.
`rightDerivedDesc_commShift` provides this compatibility for the original native
`rightDerivedDesc` when its defining transformation commutes with shifts.
Neither the descent nor the transformation is assumed invertible. General
flat base change uses this result before the shared bounded-below Postnikov
comparison.
