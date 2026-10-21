/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Rees.AffineCoordinatesImage
public import Aglib.AlgebraicGeometry.Modules.IdealPowers.AffineSections
public import Aglib.RingTheory.ReesAlgebra.ModuleDirectSum

/-! # Canonical homogeneous affine Rees sections

The local comparison uses the original ideal-power inclusions, followed by
monomials in the actual polynomial module and the inverse of the geometric
image coordinates. It does not replace image coefficients by tensor products.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory Limits Opposite DirectSum

namespace AlgebraicGeometry.Scheme.Modules.Rees

open Scheme.Cohomology

variable {A : Type u} [CommRing A] (I : Ideal A)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
  (F : X.Modules) [F.IsQuasicoherent]

/-- The original ideal-power section module with the structural base-ring action. -/
abbrev powerSections (n : ℕ) (U : X.Opens) :=
  (moduleSectionsPresheaf X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
    (idealPower X (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
      F I n)).obj (op U)

/-- Restriction of the original Rees scalar action to the original base ring. -/
abbrev coefficientSectionsA (U : X.Opens) :=
  (ModuleCat.restrictScalars (algebraMap A (reesAlgebra I))).obj
    (coefficientSections I f F U)

/-- The original ideal-power inclusion gives its actual affine section image. -/
def powerSectionsEquiv (n : ℕ) (U : X.Opens) (hU : IsAffineOpen U) :
    powerSections I f F n U ≃ₗ[A]
      ↥(I ^ n • (⊤ : Submodule A (originalSections f F U))) :=
  idealMultipleAffineSectionsEquiv X
    (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
    F (I ^ n) ⟨U, hU⟩

/-- Affine Rees sections are the direct sum of the actual ideal-power sections. -/
def directSumPowerSectionsEquiv (U : X.Opens) (hU : IsAffineOpen U) :
    (⨁ n : ℕ, powerSections I f F n U) ≃ₗ[A] coefficientSectionsA I f F U := by
  letI : Module A (coefficientSections I f F U) :=
    Module.compHom _ (algebraMap A (reesAlgebra I))
  let : IsScalarTower A (reesAlgebra I) (coefficientSections I f F U) :=
    IsScalarTower.of_compHom A (reesAlgebra I) _
  exact (DirectSum.congrLinearEquiv (fun n => powerSectionsEquiv I f F n U hU)).trans
    ((I.stableFiltration (⊤ : Submodule A (originalSections f F U))).directSumSubmoduleEquiv.trans
      ((coefficientSectionsEquiv I f F U hU).restrictScalars A).symm)

/-- A homogeneous affine section enters the actual Rees image. -/
def homogeneousSectionMap (n : ℕ) (U : X.Opens) (hU : IsAffineOpen U) :
    powerSections I f F n U →ₗ[A] coefficientSectionsA I f F U :=
  (directSumPowerSectionsEquiv I f F U hU).toLinearMap.comp
    (DirectSum.lof A ℕ (fun n => powerSections I f F n U) n)

/-- Its original polynomial coordinate is precisely the homogeneous monomial
of the original ideal-power inclusion. -/
theorem homogeneousSectionMap_polynomial (n : ℕ) (U : X.Opens) (hU : IsAffineOpen U)
    (m : powerSections I f F n U) :
    (coefficientSectionsEquiv I f F U hU
      (homogeneousSectionMap I f F n U hU m)).val =
      PolynomialModule.single A n
        (show originalSections f F U from (idealMultipleι X
          (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom)
          F (I ^ n)).app U m) := by
  change (coefficientSectionsEquiv I f F U hU
    ((coefficientSectionsEquiv I f F U hU).symm
      ((I.stableFiltration (⊤ : Submodule A (originalSections f F U))).directSumSubmoduleEquiv
        (DirectSum.congrLinearEquiv (fun k => powerSectionsEquiv I f F k U hU)
          (DirectSum.lof A ℕ (fun k => powerSections I f F k U) n m))))).val = _
  rw [LinearEquiv.apply_symm_apply]
  rw [DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof]
  exact Ideal.Filtration.directSumSubmoduleEquiv_lof
    (I.stableFiltration (⊤ : Submodule A (originalSections f F U)))
    n (powerSectionsEquiv I f F n U hU m)

end AlgebraicGeometry.Scheme.Modules.Rees
