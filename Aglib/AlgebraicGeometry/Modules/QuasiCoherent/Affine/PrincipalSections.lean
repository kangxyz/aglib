/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.FiniteTypeRestriction
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Principal restriction sections of arbitrary quasicoherent modules

The localization maps are the actual sheaf restriction maps, not maps between
chosen associated sheaves. Their Hom localization comparison retains the
original restricted morphism.
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite AlgebraicGeometry
open scoped ModuleCat.Algebra
universe u
namespace AlgebraicGeometry.Scheme.Modules.QuasiCoherent
variable (R : CommRingCat.{u}) (r : R)

/-- Actual global sections of actual principal-open restriction. -/
abbrev principalGlobalSections (M : (Spec R).Modules) : ModuleCat.{u} (Localization.Away r) :=
  moduleSpecΓFunctor.obj (M.restrict (principalOpen R r))

/-- Actual principal-restriction sections have the original section action over `R`. -/
def principalGlobalSectionsEquiv (M : (Spec R).Modules) :
    principalGlobalSections R r M ≃ₗ[R]
      (modulesSpecToSheaf.obj M).presheaf.obj (.op (principalOpen R r ''ᵁ ⊤)) where
  __ := AddEquiv.refl _
  map_smul' a m := _root_.AlgebraicGeometry.Scheme.Modules.restrictAppIso_smul_Spec
    (CommRingCat.ofHom (algebraMap R (Localization.Away r))) a m

/-- The original restriction from global sections to the actual principal restriction. -/
def toPrincipalGlobalSections (M : (Spec R).Modules) :
    moduleSpecΓFunctor.obj M →ₗ[R] principalGlobalSections R r M :=
  (principalGlobalSectionsEquiv R r M).symm.toLinearMap.comp
    ((modulesSpecToSheaf.obj M).presheaf.map
      (principalOpen R r ''ᵁ ⊤).leTop.op).hom

/-- Quasicoherent principal restriction is localization of actual global sections. -/
theorem toPrincipalGlobalSections_isLocalized (M : (Spec R).Modules) [M.IsQuasicoherent] :
    IsLocalizedModule.Away r (toPrincipalGlobalSections R r M) := by
  have hlocal := (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance r
  have he : principalOpen R r ''ᵁ ⊤ = PrimeSpectrum.basicOpen r := by
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact Scheme.Hom.opensRange_localizationAway r
  have : IsLocalizedModule.Away r
      ((modulesSpecToSheaf.obj M).presheaf.map
        (principalOpen R r ''ᵁ ⊤).leTop.op).hom := by
    rw [he]
    exact hlocal
  exact IsLocalizedModule.of_linearEquiv (Submonoid.powers r) _
    (principalGlobalSectionsEquiv R r M).symm

/-- Original global-to-principal restriction is natural for actual module maps. -/
theorem toPrincipalGlobalSections_naturality {M N : (Spec R).Modules} (f : M ⟶ N)
    (m : moduleSpecΓFunctor.obj M) :
    (moduleSpecΓFunctor.map ((Scheme.Modules.restrictFunctor (principalOpen R r)).map f))
        (toPrincipalGlobalSections R r M m) =
      toPrincipalGlobalSections R r N ((moduleSpecΓFunctor.map f) m) := by
  exact PresheafOfModules.naturality_apply f.val (principalOpen R r ''ᵁ ⊤).leTop.op m

/-- Hom localization sends the original global-sections map to the original
principal-restriction map, with the extended scalar action unchanged. -/
theorem mapExtendScalars_globalSections {M N : (Spec R).Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N) :
    let := toPrincipalGlobalSections_isLocalized R r M
    let := toPrincipalGlobalSections_isLocalized R r N
    IsLocalizedModule.mapExtendScalars (Submonoid.powers r)
      (toPrincipalGlobalSections R r M) (toPrincipalGlobalSections R r N)
        (Localization.Away r) (moduleSpecΓFunctor.map f).hom =
      (moduleSpecΓFunctor.map
        ((Scheme.Modules.restrictFunctor (principalOpen R r)).map f)).hom := by
  let := toPrincipalGlobalSections_isLocalized R r M
  let := toPrincipalGlobalSections_isLocalized R r N
  apply LinearMap.restrictScalars_injective R
  apply IsLocalizedModule.linearMap_ext (Submonoid.powers r)
    (toPrincipalGlobalSections R r M) (toPrincipalGlobalSections R r N)
  ext m
  simpa only [LinearMap.restrictScalars_apply, LinearMap.comp_apply,
    IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply]
    using (toPrincipalGlobalSections_naturality R r f m).symm

end AlgebraicGeometry.Scheme.Modules.QuasiCoherent
