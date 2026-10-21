/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Detecting Hom localization through evaluation

An evaluation-compatible pair of linear equivalences transports the native
finite-presentation Hom-localization theorem to the original objects and map.
The comparison is checked before any concrete sheaf construction is supplied.
-/

@[expose] public section
noncomputable section

namespace IsLocalizedModule

variable {R : Type*} [CommRing R] (S : Submonoid R)
variable {M N M' N' H H' : Type*}
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
variable [AddCommGroup H] [AddCommGroup H']
variable [Module R M] [Module R N] [Module R M'] [Module R N']
variable [Module R H] [Module R H']
variable (f : M →ₗ[R] M') (g : N →ₗ[R] N')
variable [IsLocalizedModule S f] [IsLocalizedModule S g]
variable (Rₛ : Type*) [CommRing Rₛ] [Algebra R Rₛ] [IsLocalization S Rₛ]
variable [Module Rₛ M'] [Module Rₛ N'] [Module Rₛ H']
variable [IsScalarTower R Rₛ M'] [IsScalarTower R Rₛ N'] [IsScalarTower R Rₛ H']

/-- A map between two models of Hom modules is localization if its evaluations
commute with localization of the source and target modules. Only the source
module needs finite presentation. -/
theorem of_homEvaluation [Module.FinitePresentation R M]
    (h : H →ₗ[R] H') (e : H ≃ₗ[R] (M →ₗ[R] N))
    (e' : H' ≃ₗ[Rₛ] (M' →ₗ[Rₛ] N'))
    (hw : ∀ (x : H) (m : M), e' (h x) (f m) = g (e x m)) :
    IsLocalizedModule S h := by
  let l := mapExtendScalars S f g Rₛ
  have he : (e'.restrictScalars R).toLinearMap.comp h = l.comp e.toLinearMap := by
    apply LinearMap.ext
    intro x
    apply LinearMap.restrictScalars_injective R
    apply IsLocalizedModule.linearMap_ext S f g
    ext m
    simpa only [l, LinearMap.comp_apply, LinearMap.restrictScalars_apply, LinearEquiv.coe_coe,
      LinearEquiv.restrictScalars_apply, mapExtendScalars_apply_apply, map_apply]
      using hw x m
  have : IsLocalizedModule S l :=
    Module.FinitePresentation.isLocalizedModule_mapExtendScalars S f g Rₛ
  have hl : IsLocalizedModule S (l.comp e.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right S l e
  rw [← he] at hl
  exact (IsLocalizedModule.comp_iff_of_bijective_left S
    (e'.restrictScalars R).toLinearMap (e'.restrictScalars R).bijective).mp hl

end IsLocalizedModule
