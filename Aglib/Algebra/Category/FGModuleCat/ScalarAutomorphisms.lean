/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Algebra.Category.FGModuleCat.ScalarExtension
public import Aglib.Algebra.Category.FGModuleCat.PrincipalMultiplication
public import Aglib.Algebra.Category.FGModuleCat.Localization
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Scalar automorphisms and canonical rank-one tensor/localization conjugacies on the original
finite-module objects.

Source: `lean/R5Lab/Aglib/Algebra/Category/FGModuleCat/ScalarAutomorphisms.lean`
at frozen R5 `f8a3314ddecffcada2ec721d26d56a937bed9690`.
SHA-256: `376d4abd6dad2317e707dd5f1cbd20b70823bf2a7639b87b3b7544f9636197bf`.
Native objects and canonical maps are reused; provenance does not select declaration namespaces.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open FGModuleCat
namespace FGModuleCat
universe u

/-- Multiplication by a ring unit on an arbitrary actual finite module. -/
def finiteScalarAut (R : CommRingCat.{u}) (M : FGModuleCat.{u} R) (a : Rˣ) : Aut M :=
  (LinearEquiv.smulOfUnit a).toFGModuleCatIso

/-- Unit multiplication on the free rank-one module uses the same scalar map. -/
abbrev scalarUnitAut (R : CommRingCat.{u}) (a : Rˣ) : Aut (FGModuleCat.of R R) :=
  finiteScalarAut R (FGModuleCat.of R R) a

section ScalarExtension
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
/-- Canonical tensor-unit identification for literal scalar extension. -/
def rankOneExtensionIso :
    (finiteModuleExtension φ).obj (FGModuleCat.of R R) ≅ FGModuleCat.of S S := by
  letI := φ.hom.toAlgebra
  exact (TensorProduct.AlgebraTensorModule.rid R S S).toFGModuleCatIso

/-- The tensor-unit isomorphism carries scalar multiplication to its literal
image under the specified ring homomorphism. -/
theorem scalar_extension_square (a : Rˣ) :
    (finiteModuleExtension φ).map (scalarUnitAut R a).hom ≫ (rankOneExtensionIso φ).hom =
      (rankOneExtensionIso φ).hom ≫
        (scalarUnitAut S (Units.map φ.hom.toMonoidHom a)).hom := by
  let := φ.hom.toAlgebra
  apply FGModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | tmul s r =>
    change R at r
    change S at s
    change φ.hom ((a : R) * r) * s = (φ.hom a) * (φ.hom r * s)
    rw [map_mul, mul_assoc]
  | add x y hx hy =>
    simpa only [map_add] using congrArg₂ (· + ·) hx hy

theorem scalar_extension_conjugate (a : Rˣ) :
    Aut.autMulEquivOfIso (rankOneExtensionIso φ)
      ((finiteModuleExtension φ).mapIso (scalarUnitAut R a)) =
      scalarUnitAut S (Units.map φ.hom.toMonoidHom a) := by
  apply Iso.ext
  change (rankOneExtensionIso φ).inv ≫
    (finiteModuleExtension φ).map (scalarUnitAut R a).hom ≫ (rankOneExtensionIso φ).hom = _
  rw [scalar_extension_square]
  simp

end ScalarExtension
section LocalizedRankOne
variable (R : CommRingCat.{u}) (pi : R)
/-- The original localized rank-one module is canonically the localized ring. -/
def rankOneLocalizationIso :
    (_root_.ModuleCat.FiniteLocalization.functor (Submonoid.powers pi)).obj (FGModuleCat.of R R) ≅
      FGModuleCat.of (Localization.Away pi) (Localization.Away pi) := by
  letI : IsLocalizedModule (Submonoid.powers pi)
      ((ModuleCat.of.{u} R R).localizedModuleMkLinearMap (Submonoid.powers pi)) :=
    ModuleCat.localizedModule_isLocalizedModule (ModuleCat.of.{u} R R) (Submonoid.powers pi)
  letI : Module.Finite (Localization.Away pi)
      ((ModuleCat.of.{u} R R).localizedModule (Submonoid.powers pi)) :=
    ((ModuleCat.FiniteLocalization.functor (Submonoid.powers pi)).obj
      (FGModuleCat.of R R)).property
  exact ((IsLocalizedModule.linearEquiv (Submonoid.powers pi)
    ((ModuleCat.of.{u} R R).localizedModuleMkLinearMap (Submonoid.powers pi))
    (Algebra.linearMap R (Localization.Away pi))).extendScalarsOfIsLocalization
      (Submonoid.powers pi) (Localization.Away pi)).toFGModuleCatIso

theorem rankOneLocalizationIso_hom_apply [IsDomain R] [IsNoetherianRing R] (x : R) :
    (rankOneLocalizationIso R pi).hom
      ((ModuleCat.of.{u} R R).localizedModuleMkLinearMap (Submonoid.powers pi) x) =
    algebraMap R (Localization.Away pi) x := by
  let : IsLocalizedModule (Submonoid.powers pi)
      ((ModuleCat.of.{u} R R).localizedModuleMkLinearMap (Submonoid.powers pi)) :=
    ModuleCat.localizedModule_isLocalizedModule (ModuleCat.of.{u} R R) (Submonoid.powers pi)
  exact IsLocalizedModule.linearEquiv_apply (Submonoid.powers pi)
    ((ModuleCat.of.{u} R R).localizedModuleMkLinearMap (Submonoid.powers pi))
    (Algebra.linearMap R (Localization.Away pi)) x

/-- Actual localization of ring multiplication, in the canonical coordinates. -/
theorem localization_scalar_square [IsDomain R] [IsNoetherianRing R]
    (r : R) (a : (Localization.Away pi)ˣ)
    (ha : (a : Localization.Away pi) = algebraMap R (Localization.Away pi) r) :
    (_root_.ModuleCat.FiniteLocalization.functor (Submonoid.powers pi)).map
        (FGModuleCat.ofHom (LinearMap.mulLeft R r)) ≫ (rankOneLocalizationIso R pi).hom =
      (rankOneLocalizationIso R pi).hom ≫
        (scalarUnitAut (CommRingCat.of (Localization.Away pi)) a).hom := by
  let : Module R ((_root_.ModuleCat.FiniteLocalization.functor (Submonoid.powers pi)).obj
      (FGModuleCat.of R R)).obj :=
    inferInstanceAs (Module R ((ModuleCat.of.{u} R R).localizedModule (Submonoid.powers pi)))
  let : IsScalarTower R (Localization.Away pi)
      ((ModuleCat.FiniteLocalization.functor (Submonoid.powers pi)).obj
        (FGModuleCat.of R R)).obj :=
    inferInstanceAs (IsScalarTower R (Localization.Away pi)
      ((ModuleCat.of.{u} R R).localizedModule (Submonoid.powers pi)))
  let : IsLocalizedModule (Submonoid.powers pi)
      ((ModuleCat.of.{u} R R).localizedModuleMkLinearMap (Submonoid.powers pi)) :=
    ModuleCat.localizedModule_isLocalizedModule (ModuleCat.of.{u} R R) (Submonoid.powers pi)
  apply FGModuleCat.hom_ext
  apply LinearMap.restrictScalars_injective R
  apply IsLocalizedModule.linearMap_ext (Submonoid.powers pi)
    ((ModuleCat.of.{u} R R).localizedModuleMkLinearMap (Submonoid.powers pi))
    (Algebra.linearMap R (Localization.Away pi))
  apply LinearMap.ext
  intro x
  change (rankOneLocalizationIso R pi).hom
      ((IsLocalizedModule.mapExtendScalars (Submonoid.powers pi)
        ((ModuleCat.of.{u} R R).localizedModuleMkLinearMap (Submonoid.powers pi))
        ((ModuleCat.of.{u} R R).localizedModuleMkLinearMap (Submonoid.powers pi))
        (Localization.Away pi) (LinearMap.mulLeft R r))
          ((ModuleCat.of.{u} R R).localizedModuleMkLinearMap (Submonoid.powers pi) x)) =
    (a : Localization.Away pi) * (rankOneLocalizationIso R pi).hom
      ((ModuleCat.of.{u} R R).localizedModuleMkLinearMap (Submonoid.powers pi) x)
  rw [IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply,
    rankOneLocalizationIso_hom_apply, rankOneLocalizationIso_hom_apply, ha]
  exact map_mul (algebraMap R (Localization.Away pi)) r x

/-- The literal localized pi automorphism is multiplication by the same
localized unit, through the canonical rank-one isomorphism. -/
theorem localizedPiAut_conjugate [IsDomain R] [IsNoetherianRing R]
    (hpi : pi ≠ 0) (a : (Localization.Away pi)ˣ)
    (ha : (a : Localization.Away pi) = algebraMap R (Localization.Away pi) pi) :
    Aut.autMulEquivOfIso (rankOneLocalizationIso R pi)
      (PrincipalMultiplication.localizedPiAut R pi hpi) =
      scalarUnitAut (CommRingCat.of (Localization.Away pi)) a := by
  apply Iso.ext
  change (rankOneLocalizationIso R pi).inv ≫
    (_root_.ModuleCat.FiniteLocalization.functor (Submonoid.powers pi)).map
      (FGModuleCat.ofHom (LinearMap.mulLeft R pi)) ≫ (rankOneLocalizationIso R pi).hom = _
  rw [localization_scalar_square R pi pi a ha]
  simp

end LocalizedRankOne
end FGModuleCat
