/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.SupportBound

/-! The numerical bound uses actual support dimension, including dimension zero. -/

@[expose] public noncomputable section

open AlgebraicGeometry TopologicalSpace AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.QuasiCoherent
open AlgebraicGeometry.Scheme.Cohomology

universe u

example (k : Type u) [Field k] [Infinite k] (ι : Type u) (n : ℕ)
    (e : ι ≃ Fin (n + 1)) (F : (ProjectiveSpace k ι).Modules)
    (hF : affineLocallyFiniteType _ F) (hd : topologicalKrullDim (support F) ≤ 0) :
    (projectiveHilbertPolynomial k ι F).natDegree = 0 := by
  exact Nat.eq_zero_of_le_zero
    (natDegree_projectiveHilbertPolynomial_le_of_supportDimension_le k ι n e 0 F hF hd)

end
