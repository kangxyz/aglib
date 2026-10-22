/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineReductionCoordinates

/-! # Affine reduction coordinates before specializing a formal system -/

@[expose] public noncomputable section
open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.Coherent

universe u
variable (B : CommRingCat.{u}) (K : (Spec B).IdealSheafData)
  (M N : (Spec B).Modules) [M.IsQuasicoherent] (n : ℕ)

/-- Geometric specialization of the abstract reduction coordinates with
independent coefficient objects and original quotient-unit equation. -/
def affineQuotientReductionCoordinates
    (d : (idealSheafQuotientFunctor (Spec B) (K ^ n)).obj M ≅ N)
    (t : M ⟶ N)
    (ht : (idealSheafQuotientUnit (Spec B) (K ^ n)).app M ≫ d.hom = t) :
    {c : (moduleSpecΓFunctor.obj M ⧸
        (affineIdeal B K ^ n • (⊤ : Submodule B (moduleSpecΓFunctor.obj M)))) ≃ₗ[B]
          moduleSpecΓFunctor.obj N //
      ∀ x, c (Submodule.Quotient.mk x) = moduleSpecΓFunctor.map t x} :=
  quotientReductionCoordinatesOfComparison moduleSpecΓFunctor (affineIdeal B K ^ n)
    ((idealSheafQuotientUnit (Spec B) (K ^ n)).app M)
    (affineQuotientComparison B K M n) d t ht

end AlgebraicGeometry.Scheme.Modules.Coherent
