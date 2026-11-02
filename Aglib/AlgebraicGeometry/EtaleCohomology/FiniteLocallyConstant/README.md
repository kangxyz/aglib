# Finite locally constant coefficient comparisons

[CoefficientSquare](CoefficientSquare.lean) retains the original inverse-image
and coefficient maps. Its H1 square uses the complete value calculation in
[Functor.CoefficientSquare](../../../CategoryTheory/Functor/CoefficientSquare.lean),
with the original composition and coefficient-naturality laws, ordinary
coefficient equation and four independent Ext worlds.

[TriangleCoherence.Basic](TriangleCoherence/Basic.lean) contains the ordinary
triangle and coefficient laws for the original inverse-image maps, without a
geometric-point or coefficient-representation choice.
[TriangleCoherence](TriangleCoherence.lean) reexports these laws and retains its
arithmetic applications. [LocalPasting](LocalPasting.lean) uses the same native
local coefficient isomorphism and the general ordinary pasting calculation.
