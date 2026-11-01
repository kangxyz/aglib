/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Hyperplane

/-! The finite difference is evaluated on the original cokernel object. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Cohomology

universe u

example (k : Type u) [Field k] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace k ι).Modules) (hF : affineLocallyFiniteType _ F)
    (ν : F ⟶ (moduleTensorLeftFunctor (ProjectiveSpace k ι) (twistingSheaf k ι 1)).obj F)
    [Mono ν] : projectiveHilbertPolynomial k ι (cokernel ν) =
      (projectiveHilbertPolynomial k ι F).comp (Polynomial.X + 1) -
        projectiveHilbertPolynomial k ι F := by
  simpa using projectiveHilbertPolynomial_cokernel_mono_twist k ι n e F hF 1 ν

end
