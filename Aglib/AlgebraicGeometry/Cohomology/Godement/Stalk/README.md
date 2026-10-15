# Stalk splittings and signed total homotopy

[Splitting](Splitting.lean), imported as `Aglib.AlgebraicGeometry.Cohomology.Godement.Stalk.Splitting`, constructs the original point projection, stalk retraction and resolution homotopy. [IntContraction](IntContraction.lean) gives the actual integer-module realization of the resolution contraction.

[TotalMatrix](TotalMatrix.lean) expresses the source/total stalk maps by the original coproduct-injection and retraction formulas. [TotalHomotopy](TotalHomotopy.lean) verifies the original sign-square/cancellation and total-homotopy comparison. The total augmentation/homotopy result retains the supplied strict lower term bound or bounded-below object where stated.

For a scheme point and bounded-below module complex, `AlgebraicGeometry.Scheme.Modules.Godement.moduleStalk_map_godementTotalUnit_f` is the active simp rule for the actual total augmentation under `moduleStalk` in integer degree `n`: it gives the original integer-module germ followed by the bidegree `(n, 0)` total injection. `godementStalkTotalUnit_f` remains available for explicit rewriting.

These are actual scalar stalks and maps, not an arbitrary choice of a split model. The bounded total proof feeds [augmentation quasi-isomorphism](../TotalComplex/README.md). Ordinary categorical exactness of totalization has its own wider scope and does not remove the bound of this homotopy calculation.
