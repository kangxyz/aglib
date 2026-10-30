# Finite locally constant coefficient comparisons

[CoefficientSquare](CoefficientSquare.lean) retains the original inverse-image
and coefficient maps. Its H1 square uses the complete value calculation in
[Functor.CoefficientSquare](../../../CategoryTheory/Functor/CoefficientSquare.lean),
with the original composition and coefficient-naturality laws, ordinary
coefficient equation and four independent Ext worlds.

[TriangleCoherence](TriangleCoherence.lean) and [LocalPasting](LocalPasting.lean)
retain the native triangle and local coefficient data together with the
geometric inputs of their existing entry points.
