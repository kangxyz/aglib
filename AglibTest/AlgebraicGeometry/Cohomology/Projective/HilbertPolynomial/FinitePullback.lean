/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Projective.HilbertPolynomial.FinitePullback

/-! The pullback law reparametrizes the actual polynomial; no rank-χ premise appears. -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProjectiveSpace
open AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.Invertible
open AlgebraicGeometry.Scheme.Cohomology

universe u

example (k : Type u) [Field k] (ι : Type u) (n : ℕ) (e : ι ≃ Fin (n + 1))
    {X : Scheme.{u}} (j : X ⟶ ProjectiveSpace k ι) [IsClosedImmersion j]
    (f : X ⟶ X) [IsAffineHom f]
    (hbase : f ≫ (j ≫ toSpec k ι) = j ≫ toSpec k ι) (c : ℕ)
    (hscale : pullbackClass f (pullbackClass j (classOf _ (twistingLineBundle k ι 1))) =
      c • pullbackClass j (classOf _ (twistingLineBundle k ι 1))) :
    projectiveHilbertPolynomial k ι ((Scheme.Modules.pushforward j).obj
      (pushforwardStructureSheaf f)) =
      (projectiveHilbertPolynomial k ι ((Scheme.Modules.pushforward j).obj
        (SheafOfModules.unit X.ringCatSheaf))).comp (Polynomial.C (c : ℚ) * Polynomial.X) :=
  projectiveHilbertPolynomial_pushforwardStructure_eq_comp_mul k ι n e j f hbase c hscale

end
