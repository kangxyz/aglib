/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.GenericComparison

/-! Generic comparison keeps the original embedding and discharges its support boundary. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Cohomology

universe u

example (k : Type u) [Field k] [Infinite k] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (j : X ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (M N : X.Modules) (hM : affineLocallyFiniteType X M) (hN : affineLocallyFiniteType X N)
    (U : X.Opens) (hη : genericPoint X ∈ U) (eU : M.restrict U.ι ≅ N.restrict U.ι)
    (d : ℕ) (hd : topologicalKrullDim X ≤ (d : ℕ)) :
    (projectiveHilbertPolynomial k ι ((Scheme.Modules.pushforward j).obj M)).coeff d =
      (projectiveHilbertPolynomial k ι ((Scheme.Modules.pushforward j).obj N)).coeff d :=
  coeff_projectiveHilbertPolynomial_pushforward_eq_of_restrictIso k ι n e j M N hM hN
    U hη eU d hd

end
