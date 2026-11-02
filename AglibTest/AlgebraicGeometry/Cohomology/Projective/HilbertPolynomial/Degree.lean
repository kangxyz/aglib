/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.Degree

/-! The actual rank is concluded from geometric scaling and the original scheme dimension. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules.Invertible AlgebraicGeometry.Scheme.Cohomology

universe u

example (k : Type u) [Field k] [Infinite k] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {X : Scheme.{u}} [IsIntegral X] (j : X ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (f : X ⟶ X) (hfree : Scheme.Hom.FiniteLocallyFree f)
    (hbase : f ≫ (j ≫ toSpec k ι) = j ≫ toSpec k ι) (c : ℕ) (hc : 0 < c)
    (hscale : pullbackClass f (pullbackClass j (classOf _ (twistingLineBundle k ι 1))) =
      c • pullbackClass j (classOf _ (twistingLineBundle k ι 1)))
    (d : ℕ) (hd : topologicalKrullDim X = (d : WithBot ℕ∞)) :
    Scheme.Hom.HasLocallyFreeRank f (c ^ d) :=
  hasLocallyFreeRank_pow_of_projective_pullback_scaling k ι n e j f hfree hbase c hc hscale d hd

end
