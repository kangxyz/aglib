# Explicit polynomial evaluation maps

`LinearInterpolation` keeps the actual polynomial prescribing values at zero
and one over a field. `PairEvaluation` constructs the ordered pair of evaluations
at two supplied points. For distinct points it proves surjectivity and identifies
the full kernel with the ideal of their product of linear factors. Downstream
finite-product and graph-chart calculations use these exact maps.
