/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Stalk
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.RingTheory.Localization.Module

/-!
# Original affine sections and stalks inside the original function field

An actual frame at the generic stalk gives a map from original affine
sections to the native function field. Quasicoherence localizes this same
map at each actual point; torsion-freeness is used only for injectivity.
No replacement fraction field, localized module or stalk model is chosen.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {A : CommRingCat.{u}} [IsDomain A]
  (M : (Spec A).Modules)
  (eη : ((moduleStalk (Spec A) (genericPoint (Spec A))).obj M) ≃ₗ[(Spec A).functionField]
    (Spec A).functionField)

/-- Original affine sections, followed by the supplied frame at the actual
generic stalk. Neither quasicoherence nor torsion-freeness is used here. -/
def affineSectionsToFunctionField :
    (moduleSpecΓFunctor (R := A)).obj M →ₗ[A] (Spec A).functionField :=
  (((ModuleCat.restrictScalars (algebraMap A (Spec A).functionField)).map
    (ModuleCat.ofHom (X := (moduleStalk (Spec A) (genericPoint (Spec A))).obj M)
      (Y := ModuleCat.of (Spec A).functionField (Spec A).functionField)
      eη.toLinearMap)).hom).comp (affineSectionsToStalk M (genericPoint (Spec A))).hom

/-- The section map is literally the original top germ followed by the same frame. -/
@[simp] theorem affineSectionsToFunctionField_apply
    (s : (moduleSpecΓFunctor (R := A)).obj M) :
    affineSectionsToFunctionField M eη s =
      eη (M.presheaf.germ ⊤ (genericPoint (Spec A)) trivial s) := by
  exact congrArg eη (affineSectionsToStalk_apply M (genericPoint (Spec A)) s)

/-- Genuine torsion-free sections inject into the original function field. -/
theorem affineSectionsToFunctionField_injective [M.IsQuasicoherent]
    [Module.IsTorsionFree A ((moduleSpecΓFunctor (R := A)).obj M)] :
    Function.Injective (affineSectionsToFunctionField M eη) := by
  let : (genericPoint (Spec A)).asIdeal.IsPrime :=
    (genericPoint (Spec A) : PrimeSpectrum A).isPrime
  have : IsLocalizedModule (genericPoint (Spec A)).asIdeal.primeCompl
      (affineSectionsToStalk M (genericPoint (Spec A))).hom :=
    affineSectionsToStalk_isLocalized M _
  apply eη.injective.comp
  apply (IsLocalizedModule.injective_iff_isRegular
    (genericPoint (Spec A)).asIdeal.primeCompl
      (affineSectionsToStalk M (genericPoint (Spec A))).hom).mpr
  intro c
  have hc : (c : A) ≠ 0 := by
    intro h
    exact c.property (h.symm ▸ (genericPoint (Spec A)).asIdeal.zero_mem)
  exact (isRegular_iff_ne_zero.mpr hc).isSMulRegular

-- These local dictionaries expose the existing native structure-stalk
-- scalar maps; they do not select a new ring or module localization.
local instance stalkAlgebra (p : PrimeSpectrum A) : Algebra A ((Spec A).presheaf.stalk p) :=
  StructureSheaf.stalkAlgebra A p

local instance stalkLocalization (p : PrimeSpectrum A) :
    IsLocalization p.asIdeal.primeCompl ((Spec A).presheaf.stalk p) :=
  StructureSheaf.IsLocalization.to_stalk A p

local instance originalStalkFieldAlgebra (p : PrimeSpectrum A) :
    Algebra ((Spec A).presheaf.stalk p) (Spec A).functionField :=
  AlgebraicGeometry.stalkFunctionFieldAlgebra (Spec A) p

local instance stalkFunctionFieldTower (p : PrimeSpectrum A) :
    IsScalarTower A ((Spec A).presheaf.stalk p) (Spec A).functionField := by
  apply IsScalarTower.of_algebraMap_eq'
  exact (congrArg CommRingCat.Hom.hom
    (StructureSheaf.toStalk_stalkSpecializes (genericPoint_specializes p))).symm

local instance restrictedStalkModule (p : PrimeSpectrum A) :
    Module ((Spec A).presheaf.stalk p)
      ((ModuleCat.restrictScalars (StructureSheaf.toStalk A p).hom).obj
        ((moduleStalk (Spec A) p).obj M)) :=
  inferInstanceAs (Module ((Spec A).presheaf.stalk p) ((moduleStalk (Spec A) p).obj M))

local instance restrictedStalkModuleTower (p : PrimeSpectrum A) :
    IsScalarTower A ((Spec A).presheaf.stalk p)
      ((ModuleCat.restrictScalars (StructureSheaf.toStalk A p).hom).obj
        ((moduleStalk (Spec A) p).obj M)) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

local instance stalkModuleLocalized [M.IsQuasicoherent] (p : PrimeSpectrum A) :
    IsLocalizedModule p.asIdeal.primeCompl (affineSectionsToStalk M p).hom :=
  affineSectionsToStalk_isLocalized M p

local instance functionFieldIdentityLocalized (p : PrimeSpectrum A) :
    IsLocalizedModule p.asIdeal.primeCompl
      (LinearMap.id : (Spec A).functionField →ₗ[A] (Spec A).functionField) :=
  isLocalizedModule_id p.asIdeal.primeCompl (Spec A).functionField
    ((Spec A).presheaf.stalk p)

/-- The original generic-section map localized at the actual point stalk,
with the original stalk-to-function-field scalar action. -/
def affineStalkToFunctionField [M.IsQuasicoherent] (p : PrimeSpectrum A) :
    ((moduleStalk (Spec A) p).obj M) →ₗ[(Spec A).presheaf.stalk p]
      (Spec A).functionField :=
  IsLocalizedModule.mapExtendScalars p.asIdeal.primeCompl
    (affineSectionsToStalk M p).hom (LinearMap.id :
      (Spec A).functionField →ₗ[A] (Spec A).functionField)
    ((Spec A).presheaf.stalk p) (affineSectionsToFunctionField M eη)

/-- The actual localized map retains the original affine section value. -/
@[simp] theorem affineStalkToFunctionField_apply [M.IsQuasicoherent] (p : PrimeSpectrum A)
    (s : (moduleSpecΓFunctor (R := A)).obj M) :
    affineStalkToFunctionField M eη p (affineSectionsToStalk M p s) =
      affineSectionsToFunctionField M eη s := by
  exact IsLocalizedModule.map_apply p.asIdeal.primeCompl
    (affineSectionsToStalk M p).hom (LinearMap.id :
      (Spec A).functionField →ₗ[A] (Spec A).functionField)
    (affineSectionsToFunctionField M eη) s

/-- Both sides use the original module germs and the same generic frame. -/
theorem affineStalkToFunctionField_germ [M.IsQuasicoherent] (p : PrimeSpectrum A)
    (s : (moduleSpecΓFunctor (R := A)).obj M) :
    affineStalkToFunctionField M eη p (M.presheaf.germ ⊤ p trivial s) =
      eη (M.presheaf.germ ⊤ (genericPoint (Spec A)) trivial s) := by
  rw [← affineSectionsToStalk_apply M p s, affineStalkToFunctionField_apply,
    affineSectionsToFunctionField_apply]

/-- Localizing the same injective section map gives an injective original stalk map. -/
theorem affineStalkToFunctionField_injective [M.IsQuasicoherent]
    [Module.IsTorsionFree A ((moduleSpecΓFunctor (R := A)).obj M)] (p : PrimeSpectrum A) :
    Function.Injective (affineStalkToFunctionField M eη p) := by
  exact IsLocalizedModule.map_injective p.asIdeal.primeCompl
    (affineSectionsToStalk M p).hom (LinearMap.id :
      (Spec A).functionField →ₗ[A] (Spec A).functionField)
    (affineSectionsToFunctionField M eη) (affineSectionsToFunctionField_injective M eη)

end AlgebraicGeometry.Scheme.Modules
