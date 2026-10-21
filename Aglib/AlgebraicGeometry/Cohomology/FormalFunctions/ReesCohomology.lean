/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesCohomologyAffine
public import Aglib.AlgebraicGeometry.Cohomology.Cech.Coproduct
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesCohomologyAction
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesCohomologyScalars
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesPresheafComparison
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesFiniteness
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.GradedCohomology
public import Mathlib.Algebra.Module.TransferInstance

/-!
# The actual finite Rees module on ideal-power cohomology

The native direct sum of the original cohomology modules is compared with
cohomology of the geometric image using the actual coproduct inclusions,
section comparison, and affine direct-image map. The structural Rees action
is transferred through this canonical comparison, without changing the
original base-ring action.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Cohomology

open Modules.Rees

variable {A : Type u} [CommRing A] (I : Ideal A)
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
  [CompactSpace X] [X.IsSeparated] (F : X.Modules) [F.IsQuasicoherent]

/-- The original structural base-ring map used throughout Rees cohomology. -/
abbrev reesCohomologyBaseScalars : A →+* Γ(X, ⊤) :=
  f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

/-- The structural Rees-ring map on the geometric Rees space. -/
abbrev reesCohomologyReesScalars : reesAlgebra I →+* Γ(space I f, ⊤) :=
  (structureMap I f).appTop.hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (reesAlgebra I))).inv.hom

local notation "α" => reesCohomologyBaseScalars f
local notation "β" => reesCohomologyReesScalars I f

/-- Canonical base-linear comparison of the original graded cohomology with the
original cohomology of the geometric Rees image. -/
def reesCohomologyEquiv (q : ℕ) :
    letI := moduleCohomologyModuleOfHom (space I f)
      ((projection I f).appTop.hom.comp α) (coefficient I f F) q
    idealPowerCohomologyTotal X α F I q ≃ₗ[A]
      Sheaf.H.{u + 1} (moduleAddSheaf (space I f) (coefficient I f F)) q := by
  letI := moduleCohomologyModuleOfHom (space I f)
    ((projection I f).appTop.hom.comp α) (coefficient I f F) q
  letI : ∀ n, (reesPowerFamily I f F n).IsQuasicoherent := fun n =>
    Modules.idealMultiple_isQuasicoherent X α F (I ^ n)
  letI : (coefficient I f F).IsQuasicoherent :=
    Modules.isQuasicoherent_affineUnitImage (polynomialProjection I f) (pulledCoefficient I f F)
  letI := moduleCohomologyModuleOfHom X α (∐ reesPowerFamily I f F) q
  letI := moduleCohomologyModuleOfHom X α (reesPushforwardCoefficient I f F) q
  exact (moduleCohomologyCoproductEquiv.{u, 0} X α (reesPowerFamily I f F) q).trans
    ((moduleSectionsCohomologyEquiv X α (reesPowerSectionsIso I f F) q).trans
      (moduleCohomologyAffinePushforwardEquiv (projection I f) (coefficient I f F) α q))

/-- On each homogeneous summand the canonical comparison retains the original
coefficient inclusion, section isomorphism, and geometric cohomology map. -/
theorem reesCohomologyEquiv_lof (q n : ℕ)
    (x : idealPowerCohomology X α F I q n) :
    reesCohomologyEquiv I f F q
      (DirectSum.lof A ℕ (fun k => ↥(idealPowerCohomology X α F I q k)) n x) =
    moduleCohomologyMapAlong (projection I f) (𝟙 (reesPushforwardCoefficient I f F)) q
      (Sheaf.H.map (moduleSectionsAddSheafMap X α (reesPowerSectionsIso I f F).hom) q
        (moduleCohomologyMapOfHom X α (Sigma.ι (reesPowerFamily I f F) n) q x)) := by
  change moduleCohomologyMapAlong _ _ q
    (Sheaf.H.map _ q (moduleCohomologyCoproductMap.{u, 0} X α (reesPowerFamily I f F) q
      (DirectSum.lof A ℕ (fun k => ↥(idealPowerCohomology X α F I q k)) n x))) = _
  rw [moduleCohomologyCoproductMap_lof.{u, 0}]

omit [CompactSpace X] [X.IsSeparated] [F.IsQuasicoherent] in
/-- The actual structural Rees action on the geometric coefficient is compatible
with the original pulled-back base-ring action. -/
theorem reesCoefficientCohomology_isScalarTower (q : ℕ) :
    letI := moduleCohomologyModuleOfHom (space I f)
      ((projection I f).appTop.hom.comp α) (coefficient I f F) q
    letI := moduleCohomologyModuleOfHom (space I f) β (coefficient I f F) q
    IsScalarTower A (reesAlgebra I)
      (Sheaf.H.{u + 1} (moduleAddSheaf (space I f) (coefficient I f F)) q) := by
  exact moduleCohomology_isScalarTower_ofHom (space I f)
    ((projection I f).appTop.hom.comp α) β
    (moduleSectionsBaseChangeScalars (projection I f) (structureMap I f) f
      (algebraMap A (reesAlgebra I)) Limits.pullback.condition) (coefficient I f F) q

/-- The actual Rees action transported along the canonical cohomology comparison.
The existing `A`-module structure on the direct sum is left unchanged. -/
abbrev reesCohomologyModule (q : ℕ) :
    Module (reesAlgebra I) (idealPowerCohomologyTotal X α F I q) := by
  letI := moduleCohomologyModuleOfHom (space I f)
    ((projection I f).appTop.hom.comp α) (coefficient I f F) q
  letI := moduleCohomologyModuleOfHom (space I f) β (coefficient I f F) q
  exact (reesCohomologyEquiv I f F q).toAddEquiv.module (reesAlgebra I)

/-- The transferred Rees action restricts to the original base-ring action. -/
theorem reesCohomology_isScalarTower (q : ℕ) :
    letI := reesCohomologyModule I f F q
    IsScalarTower A (reesAlgebra I) (idealPowerCohomologyTotal X α F I q) := by
  let := moduleCohomologyModuleOfHom (space I f)
    ((projection I f).appTop.hom.comp α) (coefficient I f F) q
  let := moduleCohomologyModuleOfHom (space I f) β (coefficient I f F) q
  let := reesCoefficientCohomology_isScalarTower I f F q
  exact LinearEquiv.isScalarTower (reesAlgebra I) (reesCohomologyEquiv I f F q)

/-- The canonical comparison is Rees-linear for the actual transported action. -/
def reesCohomologyReesEquiv (q : ℕ) :
    letI := reesCohomologyModule I f F q
    letI := moduleCohomologyModuleOfHom (space I f) β (coefficient I f F) q
    idealPowerCohomologyTotal X α F I q ≃ₗ[reesAlgebra I]
      Sheaf.H.{u + 1} (moduleAddSheaf (space I f) (coefficient I f F)) q := by
  letI := moduleCohomologyModuleOfHom (space I f)
    ((projection I f).appTop.hom.comp α) (coefficient I f F) q
  letI := moduleCohomologyModuleOfHom (space I f) β (coefficient I f F) q
  exact (reesCohomologyEquiv I f F q).toAddEquiv.linearEquiv (reesAlgebra I)

/-- Proper coherent cohomology finiteness gives finiteness of the canonical
Rees module on the original ideal-power cohomology, with no flatness hypothesis. -/
theorem reesCohomology_finite [IsNoetherianRing A] [IsProper f]
    (hF : Modules.QuasiCoherent.affineLocallyFiniteType X F) (q : ℕ) :
    letI := reesCohomologyModule I f F q
    Module.Finite (reesAlgebra I) (idealPowerCohomologyTotal X α F I q) := by
  let := reesCohomologyModule I f F q
  let := moduleCohomologyModuleOfHom (space I f) β (coefficient I f F) q
  let := reesCoefficient_cohomology_finite I f F hF q
  exact Module.Finite.equiv (reesCohomologyReesEquiv I f F q).symm

end AlgebraicGeometry.Scheme.Cohomology
