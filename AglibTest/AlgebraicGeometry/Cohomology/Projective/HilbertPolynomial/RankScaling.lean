/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.RankScaling

/-! The rank law concerns the top-dimensional coefficient of the original pushforward. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Cohomology

universe u

example (k : Type u) [Field k] [Infinite k] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {X : Scheme.{u}} [IsIntegral X] (j : X ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (M : X.Modules) (r : ℕ) (hr : SheafHasRank M r) (d : ℕ)
    (hd : topologicalKrullDim X ≤ (d : ℕ)) :
    (projectiveHilbertPolynomial k ι ((Scheme.Modules.pushforward j).obj M)).coeff d =
      (r : ℚ) * (projectiveHilbertPolynomial k ι ((Scheme.Modules.pushforward j).obj
        (SheafOfModules.unit X.ringCatSheaf))).coeff d :=
  coeff_projectiveHilbertPolynomial_pushforward_of_sheafHasRank k ι n e j M r hr d hd

end
