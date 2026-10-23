# The actual quotient-section complement

Import `Aglib.AlgebraicGeometry.ProjectiveBundle.RankTwoExtension.Complement`.
The input remains the original short exact sequence `O_X → E → O_X` on an
arbitrary scheme. `quotientComplement` is the open complement of the actual
quotient-section image. `complementChart` uses each original chart zero;
`complementChart_projection` and `complementChart_isPullback` retain its
coefficient triangle and cartesian square. `complementProjection_isAffine`
proves affineness over the original base by these same charts.

For an original open `W`, an actual retraction `r : E.over W → O_X.over W`
and its equation with the restricted original inclusion construct
`complementarySection`. Its local parameter is `r` applied to the original
frame lift. `complementaryParameter_transition` derives the required
translation equation from `transition_spec`; no complementary section is
assumed. `complementarySection_chart`, `complementarySection_projection`
and `complementarySection_disjoint` retain the exact local formulas,
original-open triangle and disjointness from the quotient-section image.
The map into the total bundle over an open is not asserted to be globally
closed. No field, reducedness, Noetherianity or normalization hypothesis is used.
