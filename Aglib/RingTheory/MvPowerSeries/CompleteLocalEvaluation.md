# Native evaluation in a complete local ring

Source: [CompleteLocalEvaluation.lean](CompleteLocalEvaluation.lean).

`MvPowerSeries.completeLocalEval` uses the original coefficient homomorphism
and a finite family of elements of the actual maximal ideal. Its map is native
`eval₂Hom` in the actual maximal-ideal topology. Constants, variables, residue
values and the exact image of the variable ideal are retained.

Residue-surjective coefficients and a family generating the maximal ideal give
surjectivity by the native adic lifting theorem. For two variables over a field,
the source dimension is at most two. If the target dimension is exactly two,
a nonzero evaluation kernel contradicts the existing surjective nonzerodivisor
dimension-drop theorem. Thus the SAME evaluation map is a ring equivalence.
No target Noetherianity, regularity or normality is an extra lower hypothesis.

This is not replacement of the target by a finite Cohen subring. The target
ring and original constants/parameters remain fixed. The coefficient field
here is not the later expanded differential base Lambda.

Direct consumers: [RingTheory/RegularLocalRing/FormalCoordinatesTwo](../RegularLocalRing/FormalCoordinatesTwo.md).
