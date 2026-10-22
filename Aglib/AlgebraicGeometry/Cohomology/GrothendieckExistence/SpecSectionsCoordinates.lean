/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.GrothendieckExistence.AffineQuotientModuleSections

/-! # Canonical structural scalar coordinates on original Spec sections -/

@[expose] public noncomputable section
open CategoryTheory Opposite
namespace AlgebraicGeometry.Scheme.Modules
universe u

set_option backward.isDefEq.respectTransparency false in
/-- Scalar restriction along the actual identity-base map agrees with native
Spec global sections, by the identity on section elements. -/
def identityBaseSpecSectionsIso (B : CommRingCat.{u}) (M : (Spec B).Modules) :
    (Cohomology.moduleSectionsPresheaf (Spec B) (idealThickeningBaseScalar (𝟙 (Spec B)))
      M).obj (op ⊤) ≅ moduleSpecΓFunctor.obj M := by
  have h : idealThickeningBaseScalar (𝟙 (Spec B)) = (Scheme.ΓSpecIso B).inv.hom := by
    simp [idealThickeningBaseScalar]
  exact (ModuleCat.restrictScalarsCongr h).app
    (((PresheafOfModules.forgetToPresheafModuleCat (op ⊤)
      (CategoryTheory.Limits.isTerminalTop (α := (Spec B).Opens)).op).obj M.val).obj (op ⊤))

@[simp]
theorem identityBaseSpecSectionsIso_hom_apply (B : CommRingCat.{u})
    (M : (Spec B).Modules) (x : Γ(M, ⊤)) :
    (identityBaseSpecSectionsIso B M).hom x = x := rfl

@[simp]
theorem identityBaseSpecSectionsIso_inv_apply (B : CommRingCat.{u})
    (M : (Spec B).Modules) (x : moduleSpecΓFunctor.obj M) :
    (identityBaseSpecSectionsIso B M).inv x = x := rfl

/-- An original linear equivalence identifies the corresponding ideal quotients. -/
def idealQuotientCoordinates {R : Type u} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (J : Ideal R) (e : M ≃ₗ[R] N) :
    (M ⧸ (J • (⊤ : Submodule R M))) ≃ₗ[R] N ⧸ (J • (⊤ : Submodule R N)) :=
  Submodule.Quotient.equiv _ _ e (by
    rw [Submodule.map_smul'', Submodule.map_top, LinearMap.range_eq_top.mpr e.surjective])

@[simp]
theorem idealQuotientCoordinates_mk {R : Type u} [CommRing R]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (J : Ideal R) (e : M ≃ₗ[R] N) (x : M) :
    idealQuotientCoordinates J e (Submodule.Quotient.mk x) =
      Submodule.Quotient.mk (e x) := rfl

end AlgebraicGeometry.Scheme.Modules
