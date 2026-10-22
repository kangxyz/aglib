/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.Completion
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.AffineQuotientSections

/-! # Original affine-section coordinates for native ideal-sheaf quotients

The geometric quotient comparison is the existing completion comparison.
Only its actual section coordinates are assembled here.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules

universe u
variable {B : Type u} [CommRing B] {X : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of B)) (J : Ideal B)
  (M : X.Modules) [M.IsQuasicoherent]

/-- Original quotient sections over the structural coefficient ring. -/
def generatedIdealQuotientSectionsEquiv (U : X.affineOpens) (n : ℕ) :
    letI := idealSectionModule X (idealThickeningBaseScalar f) M U.val
    letI := idealSectionModule X (idealThickeningBaseScalar f)
      ((Coherent.idealSheafQuotientFunctor X (idealThickeningIdealSheaf f J ^ n)).obj M) U.val
    (Γ(M, U.val) ⧸ (J ^ n • ⊤ : Submodule B Γ(M, U.val))) ≃ₗ[B]
      Γ((Coherent.idealSheafQuotientFunctor X (idealThickeningIdealSheaf f J ^ n)).obj M,
        U.val) := by
  let c := Cohomology.idealPowerQuotientIdealSheafIso f J M n
  let e := ((Cohomology.moduleSectionsPresheafFunctor X (idealThickeningBaseScalar f)) ⋙
    (CategoryTheory.evaluation _ _).obj (op U.val)).mapIso c
  exact (idealQuotientAffineSectionsEquiv f M (J ^ n) U).trans e.toLinearEquiv

theorem generatedIdealQuotientSectionsEquiv_mk (U : X.affineOpens) (n : ℕ)
    (s : Γ(M, U.val)) :
    letI := idealSectionModule X (idealThickeningBaseScalar f) M U.val
    generatedIdealQuotientSectionsEquiv f J M U n (Submodule.Quotient.mk s) =
      ((Coherent.idealSheafQuotientUnit X (idealThickeningIdealSheaf f J ^ n)).app M).app
        U.val s := by
  change (Cohomology.idealPowerQuotientIdealSheafIso f J M n).hom.app U.val
    ((idealQuotientπ X (idealThickeningBaseScalar f) M (J ^ n)).app U.val s) = _
  exact congrArg (fun g => g.app U.val s)
    (Cohomology.idealQuotientπ_idealSheafIso_hom f J M n)

end AlgebraicGeometry.Scheme.Modules
