# Finite coproducts in preadditive categories

[Coproducts](Coproducts.lean), imported as `Aglib.CategoryTheory.Preadditive.Coproducts`, proves `CategoryTheory.Limits.Sigma.sum_π_ι`: in a preadditive category the projections `Sigma.π f j` and inclusions `Sigma.ι f j` of a finite coproduct sum to the identity. Hence every morphism into a finite coproduct is the sum of its components (`exists_eq_sum_sigma_ι`). `isZero_obj_of_isBilimit` shows that an additive functor vanishes on the point of a finite bilimit bicone when it vanishes on every summand. Mathlib supplies `Sigma.π` and the orthogonality relations `Sigma.ι_π`; it has no sum formula for them.

The consumers are the [global-section generators](../../AlgebraicGeometry/Modules/Generators/GlobalSections.lean) of scheme modules and the finite-coproduct cohomology vanishing of [Cohomology/Exact/Modules](../../AlgebraicGeometry/Cohomology/Exact/Modules.lean).
