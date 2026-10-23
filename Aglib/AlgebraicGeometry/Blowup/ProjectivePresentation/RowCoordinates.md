# Coefficients of the original affine presentation row

[RowCoordinates.lean](RowCoordinates.lean) retains the actual original
quotient and chart-frame maps. The native affine tilde comparison recovers
the coefficient map on `T ⊗[S] (S ⊗[R] I)`, including possible torsion.
The original ideal sections determine its pure-tensor formula.

`framedFamily_coefficient_of_scalarExtension` applies that proved formula
to an actual S-linear map with the same pure-tensor ratios. Its concrete
consumer is the original scalar ratio map in `ChartCoordinates`. The result
is the actual original indexed framed-row equation, with no supplied row
compatibility, closedness, projectivity, or flatness assumption.
