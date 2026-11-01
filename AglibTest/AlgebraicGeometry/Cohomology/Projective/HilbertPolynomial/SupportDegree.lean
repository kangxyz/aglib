/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.SupportDegree

/-! The degree is computed from the original nonzero coherent support, with no degree premise. -/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProjectiveSpace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent AlgebraicGeometry.Scheme.Cohomology

universe u

example (k : Type u) [Field k] [Infinite k] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    (F : (ProjectiveSpace k ι).Modules) (hF : affineLocallyFiniteType _ F) (hne : ¬ IsZero F) :
    topologicalKrullDim (support F) =
      ((projectiveHilbertPolynomial k ι F).natDegree : WithBot ℕ∞) :=
  topologicalKrullDim_support_eq_natDegree_projectiveHilbertPolynomial k ι n e F hF hne

end
