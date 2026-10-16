/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Differentials.Relative.AffineBase
public import Aglib.AlgebraicGeometry.Modules.Differentials.Affine

/-!
# Actual relative differentials on affine schemes

The sole relative differential sheaf for the original morphism `Spec.map σ`
is canonically the tilde of the native Kähler module of `σ`. The comparison
uses the original affine-base universal derivation and the original
localization seed. It preserves the literal differential on every principal
open and proves quasicoherence, for arbitrary commutative rings.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Opposite

namespace AlgebraicGeometry.Scheme.Modules.Differentials

universe u

variable {A B : CommRingCat.{u}} (σ : A ⟶ B)

/-- The original constants of the spectrum morphism are the original localized ring map. -/
theorem affineBaseConstants_specMap :
    affineBaseConstants (Spec.map σ) = affineRelativeConstants σ := by
  apply NatTrans.ext
  funext U
  have h : (Scheme.ΓSpecIso A).inv ≫ (Spec.map σ).appTop =
      σ ≫ (Scheme.ΓSpecIso B).inv :=
    (Scheme.ΓSpecIso_inv_naturality σ).symm
  exact congrArg (fun k : A ⟶ Γ(Spec B, ⊤) =>
    k ≫ (Spec B).presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op) h

/-- The affine ring differential is a derivation for the original spectrum-map constants,
with the identical differential values. -/
def affineConstantDerivationFromSpec : PresheafOfModulesOfCommRing.Derivation'
    (affineRelativeDifferentials σ) (affineBaseConstants (Spec.map σ)) where
  d := (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
    (affineRelativeConstants σ)).d
  d_mul := (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
    (affineRelativeConstants σ)).d_mul
  d_map := (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
    (affineRelativeConstants σ)).d_map
  d_app {U} r := by
    have h := congrArg (fun t => t.app U) (affineBaseConstants_specMap σ)
    exact (congrArg
      (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
        (affineRelativeConstants σ)).d
      (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) r)).trans
      ((PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
        (affineRelativeConstants σ)).d_app r)

/-- The original spectrum-map constant differential is a derivation for the original affine
ring constants, with the identical differential values. -/
def affineSpecDerivationFromConstants : PresheafOfModulesOfCommRing.Derivation'
    (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
      (affineBaseConstants (Spec.map σ))) (affineRelativeConstants σ) where
  d := (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
    (affineBaseConstants (Spec.map σ))).d
  d_mul := (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
    (affineBaseConstants (Spec.map σ))).d_mul
  d_map := (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
    (affineBaseConstants (Spec.map σ))).d_map
  d_app {U} r := by
    have h := congrArg (fun t => t.app U) (affineBaseConstants_specMap σ).symm
    exact (congrArg
      (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
        (affineBaseConstants (Spec.map σ))).d
      (DFunLike.congr_fun (congrArg CommRingCat.Hom.hom h) r)).trans
      ((PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
        (affineBaseConstants (Spec.map σ))).d_app r)

/-- The original universal derivations identify the two native constant-base presheaves
for the spectrum morphism. -/
def affineBaseDifferentialPresheafSpecIso :
    PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
      (affineBaseConstants (Spec.map σ)) ≅ affineRelativeDifferentials σ := by
  let g := (PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal'
    (affineBaseConstants (Spec.map σ))).desc (affineConstantDerivationFromSpec σ)
  let h := (PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal'
    (affineRelativeConstants σ)).desc (affineSpecDerivationFromConstants σ)
  have hg (U : (Spec B).Opensᵒᵖ) (a : (Spec B).presheaf.obj U) :
      g.app U ((PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
        (affineBaseConstants (Spec.map σ))).d a) =
      (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
        (affineRelativeConstants σ)).d a :=
    PresheafOfModulesOfCommRing.Derivation.congr_d
      ((PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal'
        (affineBaseConstants (Spec.map σ))).fac (affineConstantDerivationFromSpec σ)) a
  have hh (U : (Spec B).Opensᵒᵖ) (a : (Spec B).presheaf.obj U) :
      h.app U ((PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
        (affineRelativeConstants σ)).d a) =
      (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
        (affineBaseConstants (Spec.map σ))).d a :=
    PresheafOfModulesOfCommRing.Derivation.congr_d
      ((PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal'
        (affineRelativeConstants σ)).fac (affineSpecDerivationFromConstants σ)) a
  refine ⟨g, h, ?_, ?_⟩
  · apply (PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal'
      (affineBaseConstants (Spec.map σ))).postcomp_injective
    ext U a
    exact (congrArg (h.app U) (hg U a)).trans (hh U a)
  · apply (PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal'
      (affineRelativeConstants σ)).postcomp_injective
    ext U a
    exact (congrArg (g.app U) (hh U a)).trans (hg U a)

private lemma affineBaseDifferentialPresheafSpecIso_d
    (U : (Spec B).Opensᵒᵖ) (a : (Spec B).presheaf.obj U) :
    (affineBaseDifferentialPresheafSpecIso σ).hom.app U
      ((PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
        (affineBaseConstants (Spec.map σ))).d a) =
    (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
      (affineRelativeConstants σ)).d a :=
  PresheafOfModulesOfCommRing.Derivation.congr_d
    ((PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal'
      (affineBaseConstants (Spec.map σ))).fac (affineConstantDerivationFromSpec σ)) a

/-- The two native constant-base presentations agree through their original universal
derivations and the original module sheafification. -/
def affineBaseDifferentialSheafSpecIso : affineBaseDifferentialSheaf (Spec.map σ) ≅
    (PresheafOfModules.sheafification (𝟙 (Spec B).ringCatSheaf.obj)).obj
      (affineRelativeDifferentials σ) :=
  (PresheafOfModules.sheafification (𝟙 (Spec B).ringCatSheaf.obj)).mapIso
    (affineBaseDifferentialPresheafSpecIso σ)

/-- The presentation comparison preserves the original sheafified differential on every open. -/
theorem affineBaseDifferentialSheafSpecIso_hom_d
    (U : (Spec B).Opensᵒᵖ) (a : (Spec B).presheaf.obj U) :
    (affineBaseDifferentialSheafSpecIso σ).hom.val.app U
      ((CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology (Spec B))
        (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
          (affineBaseConstants (Spec.map σ))).presheaf).app U
        ((PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
          (affineBaseConstants (Spec.map σ))).d a)) =
    (CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology (Spec B))
      (affineRelativeDifferentials σ).presheaf).app U
      ((PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
        (affineRelativeConstants σ)).d a) := by
  have H := congrArg (fun t => t.app U)
    (CategoryTheory.toSheafify_naturality
      (J := _root_.Opens.grothendieckTopology (Spec B))
      ((PresheafOfModules.toPresheaf (Spec B).ringCatSheaf.obj).map
        (affineBaseDifferentialPresheafSpecIso σ).hom))
  have H' := ConcreteCategory.congr_hom H
    ((PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation'
      (affineBaseConstants (Spec.map σ))).d a)
  exact H'.symm.trans (congrArg
    ((CategoryTheory.toSheafify (_root_.Opens.grothendieckTopology (Spec B))
      (affineRelativeDifferentials σ).presheaf).app U)
        (affineBaseDifferentialPresheafSpecIso_d σ U a))

/-- Actual scheme-relative differentials on an affine spectrum are the tilde of the original
ring-theoretic Kähler module. -/
def relativeDifferentialAffineIso : relativeDifferentialSheaf (Spec.map σ) ≅
    tilde (CommRingCat.KaehlerDifferential σ) :=
  relativeDifferentialSheafAffineBaseIso (Spec.map σ) ≪≫ affineBaseDifferentialSheafSpecIso σ ≪≫
    affineRelativeDifferentialIso σ

/-- The affine comparison sends the actual relative differential to its original localized
ring differential on every principal open. -/
theorem relativeDifferentialAffineIso_hom_d (r b : B) :
    (relativeDifferentialAffineIso σ).hom.val.app (op (PrimeSpectrum.basicOpen r))
      ((relativeDifferentialDerivation (Spec.map σ)).d
        (algebraMap B Γ(Spec B, PrimeSpectrum.basicOpen r) b)) =
    tilde.toOpen (CommRingCat.KaehlerDifferential σ) (PrimeSpectrum.basicOpen r)
      (CommRingCat.KaehlerDifferential.d b) := by
  let U := op (PrimeSpectrum.basicOpen r)
  let a := algebraMap B Γ(Spec B, PrimeSpectrum.basicOpen r) b
  exact (congrArg (fun z => (affineRelativeDifferentialIso σ).hom.val.app U
    ((affineBaseDifferentialSheafSpecIso σ).hom.val.app U z))
    (relativeDifferentialSheafAffineBaseIso_hom_d (Spec.map σ) U a)).trans
    ((congrArg ((affineRelativeDifferentialIso σ).hom.val.app U)
      (affineBaseDifferentialSheafSpecIso_hom_d σ U a)).trans
        (affineRelativeDifferentialIso_hom_d σ r b))

/-- The inverse affine comparison also preserves the original localized differential. -/
theorem relativeDifferentialAffineIso_inv_d (r b : B) :
    (relativeDifferentialAffineIso σ).inv.val.app (op (PrimeSpectrum.basicOpen r))
      (tilde.toOpen (CommRingCat.KaehlerDifferential σ) (PrimeSpectrum.basicOpen r)
        (CommRingCat.KaehlerDifferential.d b)) =
    (relativeDifferentialDerivation (Spec.map σ)).d
      (algebraMap B Γ(Spec B, PrimeSpectrum.basicOpen r) b) := by
  rw [← relativeDifferentialAffineIso_hom_d σ r b]
  exact ConcreteCategory.congr_hom
    (congrArg (fun k => k.val.app (op (PrimeSpectrum.basicOpen r)))
      (relativeDifferentialAffineIso σ).hom_inv_id) _

/-- Actual relative differentials of an affine spectrum morphism are quasicoherent. -/
instance relativeDifferentialSheaf_specMap_isQuasicoherent :
    (relativeDifferentialSheaf (Spec.map σ)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec B).ringCatSheaf).prop_of_iso
    (relativeDifferentialAffineIso σ).symm inferInstance

end AlgebraicGeometry.Scheme.Modules.Differentials
