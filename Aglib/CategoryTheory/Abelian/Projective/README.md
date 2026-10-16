# Projective dimension from supplied native resolutions

[Dimension](Dimension.lean) proves
`ProjectiveResolution.ext_eq_zero_of_isZero_X` from the original native
`extMk_surjective` and zero-class formula. The category, hom and Ext
universes remain independent, and no enough-projectives assumption is
needed beyond the supplied actual resolution.

`hasProjectiveDimensionLE_of_isZero_X` turns its actual finite support
bound into Mathlib's native `HasProjectiveDimensionLE`. The
[Koszul Ext bounds](../../../Algebra/Homology/Koszul/Ext.lean) consume it
for the original weakly regular quotient resolution. The public consumer
checks both generic and arbitrary-ring cases, including the empty list.
