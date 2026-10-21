/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesCohomology
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesPresheafAction
public import Aglib.RingTheory.ReesAlgebra.Grading
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesCohomologyTransport
public import Aglib.AlgebraicGeometry.Cohomology.FormalFunctions.ReesCohomologyComponents

/-! # Homogeneous multiplication on the actual finite Rees cohomology module -/

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

local notation "α" => reesCohomologyBaseScalars f
local notation "β" => reesCohomologyReesScalars I f

/-- The cohomology comparison on a summand is induced by its actual homogeneous
section map followed by the original direct-image cohomology map. -/
theorem reesCohomologyEquiv_lof_homogeneous (q n : ℕ)
    (x : idealPowerCohomology X α F I q n) :
    reesCohomologyEquiv I f F q
      (DirectSum.lof A ℕ (fun k => ↥(idealPowerCohomology X α F I q k)) n x) =
    moduleCohomologyMapAlong (projection I f) (𝟙 (reesPushforwardCoefficient I f F)) q
      (Sheaf.H.map (moduleSectionsAddSheafMap X α (reesHomogeneousSections I f F n)) q x) := by
  rw [reesCohomologyEquiv_lof]
  exact congrArg
    (moduleCohomologyMapAlong (projection I f) (𝟙 (reesPushforwardCoefficient I f F)) q)
    (moduleSectionsCohomology_coefficient_comp X α (Sigma.ι (reesPowerFamily I f F) n)
      (reesPowerSectionsIso I f F).hom q x).symm

/-- In cohomological degree zero every summand is sent by its original global
homogeneous section map, including the zeroth ideal power. -/
theorem reesCohomologyEquiv_lof_equiv₀ (n : ℕ)
    (x : idealPowerCohomology X α F I 0 n) :
    Sheaf.H.equiv₀ (moduleAddSheaf (space I f) (coefficient I f F)) isTerminalTop
      (reesCohomologyEquiv I f F 0
        (DirectSum.lof A ℕ (fun k => ↥(idealPowerCohomology X α F I 0 k)) n x)) =
      (pushforwardSectionsIso (projection I f)).hom.app
        (moduleAddSheaf (space I f) (coefficient I f F))
        ((reesHomogeneousSections I f F n).app (op ⊤)
          (Sheaf.H.equiv₀ (moduleAddSheaf X (reesPowerFamily I f F n)) isTerminalTop x)) := by
  rw [reesCohomologyEquiv_lof_homogeneous, moduleCohomologyMapAlong_equiv₀]
  have hid := (SheafOfModules.toSheaf.{u} X.ringCatSheaf).map_id
    (reesPushforwardCoefficient I f F)
  rw [hid]
  change (pushforwardSectionsIso (projection I f)).hom.app
    (moduleAddSheaf (space I f) (coefficient I f F))
    (Sheaf.H.equiv₀ (moduleAddSheaf X (reesPushforwardCoefficient I f F)) isTerminalTop
      (Sheaf.H.map (moduleSectionsAddSheafMap X α (reesHomogeneousSections I f F n)) 0 x)) = _
  exact congrArg
    ((pushforwardSectionsIso (projection I f)).hom.app
      (moduleAddSheaf (space I f) (coefficient I f F)))
    ((Sheaf.H.equiv₀_naturality isTerminalTop
      (moduleSectionsAddSheafMap X α (reesHomogeneousSections I f F n)) x).symm)

/-- The transferred action of each native homogeneous Rees element is the
original ideal-power multiplication map on the original cohomology summand. -/
theorem reesCohomology_monomial_lof (q r n : ℕ) (a : ↥(I ^ r))
    (x : idealPowerCohomology X α F I q n) :
    letI := reesCohomologyModule I f F q
    (reesAlgebra.homogeneous I r a : reesAlgebra I) •
        DirectSum.lof A ℕ (fun k => ↥(idealPowerCohomology X α F I q k)) n x =
      DirectSum.lof A ℕ (fun k => ↥(idealPowerCohomology X α F I q k)) (r + n)
        (moduleCohomologyMapOfHom X α (Modules.idealPowerMul X α F I r n a) q x) := by
  let := reesCohomologyModule I f F q
  let := moduleCohomologyModuleOfHom (space I f)
    ((projection I f).appTop.hom.comp α) (coefficient I f F) q
  let := moduleCohomologyModuleOfHom (space I f) β (coefficient I f F) q
  apply (reesCohomologyEquiv I f F q).module_smul_eq_of_apply_eq
  rw [reesCohomologyEquiv_lof_homogeneous, reesCohomologyEquiv_lof_homogeneous]
  exact (moduleSectionsPushforwardCohomology_homogeneous (projection I f) α
    (coefficient I f F) (Modules.idealPowerMul X α F I r n a)
    (reesHomogeneousSections I f F n) (reesHomogeneousSections I f F (r + n))
    (β (reesAlgebra.homogeneous I r a : reesAlgebra I))
    (reesHomogeneousSections_mul I f F r n a) q x)

end AlgebraicGeometry.Scheme.Cohomology
