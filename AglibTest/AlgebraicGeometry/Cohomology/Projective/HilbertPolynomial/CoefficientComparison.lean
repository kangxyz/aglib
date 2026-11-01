/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.CoefficientComparison

/-! The intrinsic coefficient comparison carries no chosen common coherent module. -/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Cohomology

universe u

example (k : Type u) [Field k] [Infinite k] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    (M N : (ProjectiveSpace k ι).Modules) (hM : affineLocallyFiniteType _ M)
    (hN : affineLocallyFiniteType _ N) (U : (ProjectiveSpace k ι).Opens)
    (eU : M.restrict U.ι ≅ N.restrict U.ι) (d : ℕ)
    (hd : topologicalKrullDim
      (((support M ∪ support N) ∩ (U : Set (ProjectiveSpace k ι))ᶜ) : Set (ProjectiveSpace k ι)) <
      (d : ℕ)) :
    (projectiveHilbertPolynomial k ι M).coeff d = (projectiveHilbertPolynomial k ι N).coeff d :=
  coeff_projectiveHilbertPolynomial_eq_of_restrictIso k ι n e M N hM hN U eU d hd

end
