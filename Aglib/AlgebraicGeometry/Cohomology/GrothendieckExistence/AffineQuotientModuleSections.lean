/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineQuotientSections

/-! # Whole-module presentation of original affine quotient coordinates -/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
universe u
variable {B : Type u} [CommRing B] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of B)) (J : Ideal B)
  (M : X.Modules) [M.IsQuasicoherent]

/-- Use the native module object as a shared head before scalar specialization. -/
def generatedIdealQuotientModuleSectionsEquiv (U : X.affineOpens) (n : ℕ) :
    (((Cohomology.moduleSectionsPresheaf X (idealThickeningBaseScalar f) M).obj
      (op U.val)) ⧸ (J ^ n • (⊤ : Submodule B
        ((Cohomology.moduleSectionsPresheaf X (idealThickeningBaseScalar f) M).obj
          (op U.val))))) ≃ₗ[B]
      (Cohomology.moduleSectionsPresheaf X (idealThickeningBaseScalar f)
        ((Coherent.idealSheafQuotientFunctor X (idealThickeningIdealSheaf f J ^ n)).obj M)).obj
          (op U.val) :=
  generatedIdealQuotientSectionsEquiv f J M U n

theorem generatedIdealQuotientModuleSectionsEquiv_mk (U : X.affineOpens) (n : ℕ)
    (x : (Cohomology.moduleSectionsPresheaf X (idealThickeningBaseScalar f) M).obj
      (op U.val)) :
    generatedIdealQuotientModuleSectionsEquiv f J M U n (Submodule.Quotient.mk x) =
      ((Cohomology.moduleSectionsPresheafFunctor X (idealThickeningBaseScalar f)).map
        ((Coherent.idealSheafQuotientUnit X (idealThickeningIdealSheaf f J ^ n)).app M)).app
          (op U.val) x :=
  generatedIdealQuotientSectionsEquiv_mk f J M U n x

end AlgebraicGeometry.Scheme.Modules
