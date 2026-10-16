/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Localization.AffineSheafification
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.RingTheory.Etale.Kaehler

/-!
# Affine constant-base differentials over arbitrary commutative rings

The original constant-base differential presheaf on `Spec R` has the native
Kähler module as a localization seed. The sole general affine-localization
comparison identifies its actual module sheafification with the original
tilde module. The seed sends `d a` to the differential of the original
localized ring section. No field, smoothness, or cohomology import is used.

Sole-owner extraction of the second generic block of
`Modules/Differentials/SmoothRank.lean`, admitted from Aglib revision
`40af743`. Original source: R5Lab
`AlgebraicGeometry/Curves/Differentials/SmoothRank.lean`, frozen revision
`79307ff88f07d34fd5c3edb859f799c55e38f290`, source SHA-256
`bab90251fd10024bc7477d90539648aa6b08e4047f6d288f0e755b0b852443b5`.
The native differential namespace owns the implementation; the former
SmoothRank qualified names remain compatibility exports.
-/

@[expose] public section

noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme.Modules.Differentials
universe u
variable {F R : CommRingCat.{u}} (f : F ⟶ R)

/-- The structural ring map gives constants on all opens of its affine target. -/
def affineRelativeConstants :
    (Functor.const (Spec R).Opensᵒᵖ).obj F ⟶ (Spec R).presheaf where
  app U := f ≫ CommRingCat.ofHom (algebraMap R Γ(Spec R, U.unop))
  naturality {U V} i := by
    simp only [Functor.const_obj_map, Category.assoc]
    rfl

/-- The actual relative differential presheaf of the affine structural map. -/
abbrev affineRelativeDifferentials : (Spec R).PresheafOfModules :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
    (affineRelativeConstants f)

/-- The canonical localization map from ring differentials on the indicated affine open. -/
def affineRelativeSeedApp (U : (Spec R).Opensᵒᵖ) :
    CommRingCat.KaehlerDifferential f ⟶
      (affinePresheafModules (affineRelativeDifferentials f)).obj U := by
  let g : R ⟶ (Spec R).presheaf.obj U :=
    CommRingCat.ofHom (algebraMap R Γ(Spec R, U.unop))
  let q := CommRingCat.KaehlerDifferential.map
    (g := 𝟙 F) (g' := g) (f := f) (f' := (affineRelativeConstants f).app U)
    (by simp [affineRelativeConstants, g])
  exact ModuleCat.ofHom (Y := (affinePresheafModules (affineRelativeDifferentials f)).obj U)
    { toFun := q
      map_add' := q.hom.map_add
      map_smul' := q.hom.map_smul }

@[simp]
theorem affineRelativeSeedApp_d (U : (Spec R).Opensᵒᵖ) (a : R) :
    affineRelativeSeedApp f U (CommRingCat.KaehlerDifferential.d a) =
      CommRingCat.KaehlerDifferential.d (algebraMap R Γ(Spec R, U.unop) a) := by
  apply CommRingCat.KaehlerDifferential.map_d
  simp [affineRelativeConstants]

/-- The canonical localization maps from the ring differential module to the affine
differential presheaf. -/
def affineRelativeSeed :
    (Functor.const (Spec R).Opensᵒᵖ).obj (CommRingCat.KaehlerDifferential f) ⟶
      affinePresheafModules (affineRelativeDifferentials f) where
  app := affineRelativeSeedApp f
  naturality {U V} i := by
    apply CommRingCat.KaehlerDifferential.ext
    intro a
    change affineRelativeSeedApp f V (CommRingCat.KaehlerDifferential.d a) =
      (affineRelativeDifferentials f).map i
        (affineRelativeSeedApp f U (CommRingCat.KaehlerDifferential.d a))
    rw [affineRelativeSeedApp_d, affineRelativeSeedApp_d]
    erw [PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d]
    rfl

/-- The canonical differential seed is module localization on each principal affine open. -/
theorem affineRelativeSeed_localizing (r : R) :
    IsLocalizedModule.Away r
      ((affineRelativeSeed f).app (op (PrimeSpectrum.basicOpen r))).hom := by
  let : Algebra F R := f.hom.toAlgebra
  let : Algebra F Γ(Spec R, PrimeSpectrum.basicOpen r) :=
    ((affineRelativeConstants f).app (op (PrimeSpectrum.basicOpen r))).hom.toAlgebra
  have : IsScalarTower F R Γ(Spec R, PrimeSpectrum.basicOpen r) :=
    IsScalarTower.of_algebraMap_eq' rfl
  let e : Ω[Γ(Spec R, PrimeSpectrum.basicOpen r)⁄F] ≃ₗ[R]
      (affinePresheafModules (affineRelativeDifferentials f)).obj
        (op (PrimeSpectrum.basicOpen r)) := {
    __ := AddEquiv.refl _
    map_smul' a m := by
      change (a • m : Ω[Γ(Spec R, PrimeSpectrum.basicOpen r)⁄F]) =
        (algebraMap R Γ(Spec R, PrimeSpectrum.basicOpen r) a) • m
      exact (IsScalarTower.algebraMap_smul Γ(Spec R, PrimeSpectrum.basicOpen r) a m).symm }
  let := _root_.KaehlerDifferential.isLocalizedModule_map F R
    Γ(Spec R, PrimeSpectrum.basicOpen r) (.powers r)
  have he := IsLocalizedModule.of_linearEquiv (.powers r)
    (_root_.KaehlerDifferential.map F F R Γ(Spec R, PrimeSpectrum.basicOpen r)) e
  let : Module F ((affinePresheafModules (affineRelativeDifferentials f)).obj
      (op (PrimeSpectrum.basicOpen r))) := Module.compHom _ f.hom
  let : IsScalarTower F R ((affinePresheafModules (affineRelativeDifferentials f)).obj
      (op (PrimeSpectrum.basicOpen r))) := IsScalarTower.of_compHom _ _ _
  convert! he using 1
  apply Derivation.liftKaehlerDifferential_unique
  ext a
  change affineRelativeSeedApp f (op (PrimeSpectrum.basicOpen r))
      (CommRingCat.KaehlerDifferential.d a) =
    _root_.KaehlerDifferential.map F F R Γ(Spec R, PrimeSpectrum.basicOpen r)
      (_root_.KaehlerDifferential.D F R a)
  rw [affineRelativeSeedApp_d, _root_.KaehlerDifferential.map_D]
  rfl

/-- The sheafification of the actual affine differential presheaf is the tilde of the
ring-theoretic Kahler module, via its canonical localization maps. -/
def affineRelativeDifferentialIso :
    (PresheafOfModules.sheafification (𝟙 (Spec R).ringCatSheaf.obj)).obj
      (affineRelativeDifferentials f) ≅ tilde (CommRingCat.KaehlerDifferential f) :=
  affineSheafificationTildeIso _ _ (affineRelativeSeed f) (affineRelativeSeed_localizing f)

/-- The affine comparison sends the original sheafified differential of a ring element to
its original localized Kähler differential on every principal open. -/
theorem affineRelativeDifferentialIso_hom_d (r b : R) :
    (affineRelativeDifferentialIso f).hom.val.app (op (PrimeSpectrum.basicOpen r))
      ((CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology (Spec R))
        (affineRelativeDifferentials f).presheaf).app (op (PrimeSpectrum.basicOpen r))
        ((PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
          (affineRelativeConstants f)).d
          (algebraMap R Γ(Spec R, PrimeSpectrum.basicOpen r) b))) =
    tilde.toOpen (CommRingCat.KaehlerDifferential f) (PrimeSpectrum.basicOpen r)
      (CommRingCat.KaehlerDifferential.d b) := by
  have hs := affineSheafificationTildeIso_seed
    (affineRelativeDifferentials f) (CommRingCat.KaehlerDifferential f)
    (affineRelativeSeed f) (affineRelativeSeed_localizing f) r
    (CommRingCat.KaehlerDifferential.d b)
  have hseed := affineRelativeSeedApp_d f (op (PrimeSpectrum.basicOpen r)) b
  exact (congrArg (fun z =>
    (affineRelativeDifferentialIso f).hom.val.app (op (PrimeSpectrum.basicOpen r))
      ((CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology (Spec R))
        (affineRelativeDifferentials f).presheaf).app (op (PrimeSpectrum.basicOpen r)) z))
    hseed.symm).trans hs

end AlgebraicGeometry.Scheme.Modules.Differentials
