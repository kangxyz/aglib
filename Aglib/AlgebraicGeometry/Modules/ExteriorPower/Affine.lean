/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.ExteriorPower.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineSheafification
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.FiniteType.Basic
public import Aglib.LinearAlgebra.ExteriorPower.ScalarExtension
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Actual affine exterior powers and finite quasicoherence

The seed on every open is the original exterior map of tilde.toOpen.
Native exterior localization makes this seed
localizing on principal opens. The original affine sheafification comparison
then supplies the actual exterior sheaf and its pure-wedge equation.
Affine-local finite quasicoherence is preserved without a Noetherian
hypothesis; on a locally Noetherian scheme this is the coherent condition.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules.QuasiCoherent

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {R : CommRingCat.{u}} (M : ModuleCat.{u} R) (n : ℕ)

/-- The module structure of the original section object, before scalar restriction. -/
local instance sectionModule (U : (Spec R).Opensᵒᵖ) :
    Module ((Spec R).presheaf.obj U) (PresheafOfModulesOfCommRing.obj (tilde M).val U) :=
  (PresheafOfModulesOfCommRing.obj (tilde M).val U).isModule

/-- The actual exterior presheaf of the actual tilde sheaf. -/
abbrev exteriorTildePresheaf : (Spec R).PresheafOfModules :=
  PresheafOfModulesOfCommRing.exteriorPower (tilde M).val n

/-- The original section exterior map, together with its original wedge equation
and its principal-localization property. Both scalar presentations are fixed here. -/
def exteriorTildeSeedAppData (U : (Spec R).Opensᵒᵖ) :
    {l : ModuleCat.of R (⋀[R]^n M) ⟶ (affinePresheafModules (exteriorTildePresheaf M n)).obj U //
      (∀ v : Fin n → M, l (exteriorPower.ιMulti R n v) =
        exteriorPower.ιMulti (M := PresheafOfModulesOfCommRing.obj (tilde M).val U)
          ((Spec R).presheaf.obj U) n
          (fun k => tilde.toOpen M U.unop (v k))) ∧
      ∀ r : R, U = op (PrimeSpectrum.basicOpen r) → IsLocalizedModule.Away r l.hom} := by
  let S : CommRingCat.{u} := Γ(Spec R, U.unop)
  let N : ModuleCat.{u} S := PresheafOfModulesOfCommRing.obj (tilde M).val U
  let : Algebra R S :=
    inferInstanceAs (Algebra R Γ(Spec R, U.unop))
  let : Module R N := presheafModule (tilde M).val U
  let : IsScalarTower R S N := presheafModuleTower (tilde M).val U
  let f : M →ₗ[R] N := (tilde.toOpen M U.unop).hom
  let Z : ModuleCat.{u} R := (affinePresheafModules (exteriorTildePresheaf M n)).obj U
  let e : (⋀[S]^n N) ≃ₗ[R] Z := {
    __ := AddEquiv.refl _
    map_smul' a z := by
      change (a • z : ⋀[S]^n N) = (algebraMap R S a) • z
      exact (IsScalarTower.algebraMap_smul S a z).symm }
  let g : (⋀[R]^n M) →ₗ[R] (⋀[S]^n N) :=
    exteriorPower.mapAlgebra (R := R) (S := S) (M := M) (N := N) n f
  let l : ModuleCat.of R (⋀[R]^n M) ⟶ Z :=
    ModuleCat.ofHom (Y := Z) (e.toLinearMap.comp g)
  refine ⟨l, ?_, ?_⟩
  · intro v
    change exteriorPower.mapAlgebra (R := R) (S := S) (M := M) (N := N) n f
      (exteriorPower.ιMulti R n v) = exteriorPower.ιMulti S n (fun k => f (v k))
    exact exteriorPower.mapAlgebra_ιMulti (R := R) (S := S) (M := M) (N := N) n f v
  · intro r hU
    subst U
    let : IsLocalization.Away r S := by
      change IsLocalization.Away r Γ(Spec R, PrimeSpectrum.basicOpen r)
      infer_instance
    let : IsLocalizedModule.Away r f := by
      change IsLocalizedModule.Away r (tilde.toOpen M (PrimeSpectrum.basicOpen r)).hom
      infer_instance
    let : IsLocalizedModule.Away r g :=
      exteriorPower.isLocalizedModule_mapAlgebra (R := R) (S := S) (M := M) (N := N)
        (.powers r) n f
    exact IsLocalizedModule.of_linearEquiv (.powers r) g e

/-- The actual exterior seed on one original open. -/
def exteriorTildeSeedApp (U : (Spec R).Opensᵒᵖ) :
    ModuleCat.of R (⋀[R]^n M) ⟶ (affinePresheafModules (exteriorTildePresheaf M n)).obj U :=
  (exteriorTildeSeedAppData M n U).val

/-- The section seed preserves its original wedge. -/
theorem exteriorTildeSeedApp_mk (U : (Spec R).Opensᵒᵖ) (v : Fin n → M) :
    exteriorTildeSeedApp M n U (exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti (M := PresheafOfModulesOfCommRing.obj (tilde M).val U)
          ((Spec R).presheaf.obj U) n
        (fun k => tilde.toOpen M U.unop (v k)) :=
  (exteriorTildeSeedAppData M n U).property.1 v

/-- Its principal-open specialization is the original module localization. -/
theorem exteriorTildeSeedApp_localizing (r : R) :
    IsLocalizedModule.Away r
      (exteriorTildeSeedApp M n (op (PrimeSpectrum.basicOpen r))).hom :=
  (exteriorTildeSeedAppData M n (op (PrimeSpectrum.basicOpen r))).property.2 r rfl

/-- The original exterior maps of the original tilde localization sections. -/
def exteriorTildeSeed :
    (Functor.const (Spec R).Opensᵒᵖ).obj (ModuleCat.of R (⋀[R]^n M)) ⟶
      affinePresheafModules (exteriorTildePresheaf M n) where
  app := exteriorTildeSeedApp M n
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro v
    have hU := exteriorTildeSeedApp_mk M n U v
    have hV := exteriorTildeSeedApp_mk M n V v
    have hres := PresheafOfModulesOfCommRing.exteriorPower_map_mk (tilde M).val n i
      (fun k => tilde.toOpen M U.unop (v k))
    have hentries : (fun k => (tilde M).val.map i (tilde.toOpen M U.unop (v k))) =
        (fun k => tilde.toOpen M V.unop (v k)) := by
      funext k
      exact ConcreteCategory.congr_hom (tilde.toOpen_res M U.unop V.unop i.unop) (v k)
    have hw := congrArg (exteriorPower.ιMulti (M := PresheafOfModulesOfCommRing.obj (tilde M).val V)
          ((Spec R).presheaf.obj V) n) hentries
    exact hV.trans (hw.symm.trans (hres.symm.trans
      (congrArg ((exteriorTildePresheaf M n).map i) hU.symm)))

/-- The seed carries a pure wedge to the wedge of its original localized entries. -/
theorem exteriorTildeSeed_mk (U : (Spec R).Opens) (v : Fin n → M) :
    (exteriorTildeSeed M n).app (op U) (exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti (M := PresheafOfModulesOfCommRing.obj (tilde M).val (op U))
          ((Spec R).presheaf.obj (op U)) n
        (fun k => tilde.toOpen M U (v k)) :=
  exteriorTildeSeedApp_mk M n (op U) v

/-- The original exterior seed is module localization on every principal open. -/
theorem exteriorTildeSeed_localizing (r : R) :
    IsLocalizedModule.Away r
      ((exteriorTildeSeed M n).app (op (PrimeSpectrum.basicOpen r))).hom :=
  exteriorTildeSeedApp_localizing M n r

/-- The original sheafified exterior power of tilde M is tilde of the original
module exterior power. No finite-generation or freeness premise is needed. -/
def exteriorTildeIso :
    moduleExteriorPower (Spec R) (tilde M) n ≅ tilde (ModuleCat.of R (⋀[R]^n M)) :=
  affineSheafificationTildeIso (exteriorTildePresheaf M n)
    (ModuleCat.of R (⋀[R]^n M)) (exteriorTildeSeed M n)
    (exteriorTildeSeed_localizing M n)

/-- The actual comparison preserves original pure wedges on every principal open. -/
theorem exteriorTildeIso_hom_mk (r : R) (v : Fin n → M) :
    (exteriorTildeIso M n).hom.val.app (op (PrimeSpectrum.basicOpen r))
        ((SheafOfModulesOfCommRing.exteriorPowerMk (Spec R).sheaf (tilde M) n).app
          (op (PrimeSpectrum.basicOpen r))
          (fun k => tilde.toOpen M (PrimeSpectrum.basicOpen r) (v k))) =
      tilde.toOpen (ModuleCat.of R (⋀[R]^n M)) (PrimeSpectrum.basicOpen r)
        (exteriorPower.ιMulti R n v) := by
  have hs := affineSheafificationTildeIso_seed (exteriorTildePresheaf M n)
    (ModuleCat.of R (⋀[R]^n M)) (exteriorTildeSeed M n)
    (exteriorTildeSeed_localizing M n) r (exteriorPower.ιMulti R n v)
  have hseed := exteriorTildeSeed_mk M n (PrimeSpectrum.basicOpen r) v
  exact (congrArg (fun z =>
    (exteriorTildeIso M n).hom.val.app (op (PrimeSpectrum.basicOpen r))
      ((CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology (Spec R))
        (exteriorTildePresheaf M n).presheaf).app (op (PrimeSpectrum.basicOpen r)) z))
    hseed.symm).trans hs

variable (N : (Spec R).Modules) [N.IsQuasicoherent]

/-- The actual affine exterior comparison for an arbitrary quasicoherent sheaf,
using its original tilde/global-sections counit. -/
def moduleExteriorPowerAffineIso :
    moduleExteriorPower (Spec R) N n ≅
      tilde (ModuleCat.of R (⋀[R]^n (moduleSpecΓFunctor.obj N))) :=
  (moduleExteriorPowerFunctor (Spec R) n).mapIso (asIso N.fromTildeΓ).symm ≪≫
    exteriorTildeIso (moduleSpecΓFunctor.obj N) n

/-- Exterior powers of an actual affine finite quasicoherent sheaf are actual
affine finite quasicoherent sheaves. -/
theorem affineFiniteSheaf_moduleExteriorPower
    [Module.Finite R (moduleSpecΓFunctor.obj N)] :
    affineFiniteSheaf R (moduleExteriorPower (Spec R) N n) := by
  let E : ModuleCat.{u} R := ModuleCat.of R (⋀[R]^n (moduleSpecΓFunctor.obj N))
  have hE : affineFiniteSheaf R (tilde E) := by
    refine ⟨inferInstance, ?_⟩
    let e : E ≃ₗ[R] moduleSpecΓFunctor.obj (tilde E) :=
      (tilde.toTildeΓNatIso.app E).toLinearEquiv
    exact Module.Finite.of_surjective (M := E) e.toLinearMap e.surjective
  exact (affineFiniteSheaf R).prop_of_iso (moduleExteriorPowerAffineIso n N).symm hE

/-- The actual sheaf exterior power preserves the affine-local finite
quasicoherent property, without a smoothness or local-freeness hypothesis. -/
theorem moduleExteriorPower_affineLocallyFiniteType
    {X : Scheme.{u}} (M : X.Modules) (hM : affineLocallyFiniteType X M) (n : ℕ) :
    affineLocallyFiniteType X (moduleExteriorPower X M n) := by
  intro R j _
  let : (M.restrict j).IsQuasicoherent := (hM R j).1
  let : Module.Finite R (moduleSpecΓFunctor.obj (M.restrict j)) := (hM R j).2
  have h := affineFiniteSheaf_moduleExteriorPower n (M.restrict j)
  exact (affineFiniteSheaf R).prop_of_iso
    (moduleExteriorPowerRestrictionIso j M n) h

end AlgebraicGeometry.Scheme.Modules
