/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ExteriorPower.Basic
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Free.Sections
public import Aglib.LinearAlgebra.ExteriorPower.TopDegree

/-!
# The original top exterior frame of a finite free module sheaf

The top exterior power of the original rank-`n` free sheaf is canonically
the actual structure module. The forward map evaluates the original
sectionwise determinant; the inverse sends a scalar to that scalar times
the original wedge of the original free sections. Both inverse equations
are proved over an arbitrary commutative ringed site, including rank zero.
Global compatible sections are used without assuming a terminal site object.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Module

universe u v w

namespace SheafOfModulesOfCommRing

variable {C : Type v} [Category.{w} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  (R : Sheaf J CommRingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

local notation "Rᵣ" => Functor.obj (sheafCompose J (forget₂ CommRingCat RingCat)) R

/-- The actual free-section basis in the displayed finite coordinate order. -/
def freeFinSectionsBasis (n : ℕ) (X : Cᵒᵖ) :
    Basis (Fin n) (R.obj.obj X)
      ((SheafOfModules.free (R := Rᵣ) (ULift.{u} (Fin n))).val.obj X) :=
  (SheafOfModules.freeSectionsBasis Rᵣ (ULift.{u} (Fin n)) X).reindex Equiv.ulift

@[simp]
theorem freeFinSectionsBasis_apply (n : ℕ) (X : Cᵒᵖ) (i : Fin n) :
    freeFinSectionsBasis R n X i =
      (SheafOfModules.freeSection (R := Rᵣ) (ULift.up i)).val X := by
  rw [freeFinSectionsBasis, Module.Basis.reindex_apply]
  exact SheafOfModules.freeSectionsBasis_apply Rᵣ (ULift.{u} (Fin n)) X (ULift.up i)

/-- Original restrictions preserve the original ordered section basis. -/
theorem freeFinSectionsBasis_restrict (n : ℕ) {X Y : Cᵒᵖ} (f : X ⟶ Y) (i : Fin n) :
    (SheafOfModules.free (R := Rᵣ) (ULift.{u} (Fin n))).val.map f
        (freeFinSectionsBasis R n X i) = freeFinSectionsBasis R n Y i := by
  rw [freeFinSectionsBasis_apply, freeFinSectionsBasis_apply]
  exact PresheafOfModules.sections_property (SheafOfModules.freeSection (ULift.up i)) f

/-- The original determinants form a compatible alternating family. -/
def exteriorTopFreeDeterminant (n : ℕ) :
    PresheafOfModulesOfCommRing.AlternatingMap
      (SheafOfModules.free (R := Rᵣ) (ULift.{u} (Fin n))).val
      (SheafOfModules.unit Rᵣ).val n where
  app X := (freeFinSectionsBasis R n X).det
  naturality {X Y} f s := by
    let F := SheafOfModules.free (R := Rᵣ) (ULift.{u} (Fin n))
    let b := freeFinSectionsBasis R n X
    let c := freeFinSectionsBasis R n Y
    let a : F.val.obj X →ₛₗ[(R.obj.map f).hom] F.val.obj Y := F.val.restrictₛₗ f
    have ha : a ∘ b = c := by
      funext i
      exact freeFinSectionsBasis_restrict R n f i
    have H := b.exteriorPowerTopEquiv_mapSemilinear c a
      (_root_.exteriorPower.ιMulti (R.obj.obj X) n s)
    rw [_root_.exteriorPower.mapSemilinear_apply_ιMulti,
      Module.Basis.exteriorPowerTopEquiv_ιMulti,
      Module.Basis.exteriorPowerTopEquiv_ιMulti, ha, c.det_self, one_mul] at H
    exact H.symm

/-- The determinant map out of the actual top exterior free sheaf. -/
def exteriorTopFreeHom (n : ℕ) :
    exteriorPower R (SheafOfModules.free (R := Rᵣ) (ULift.{u} (Fin n))) n ⟶
      SheafOfModules.unit Rᵣ :=
  exteriorPowerDesc R _ _ n (exteriorTopFreeDeterminant R n)

/-- The original map evaluates on every canonical wedge by the original section determinant. -/
@[simp]
theorem exteriorTopFreeHom_mk (n : ℕ) (X : Cᵒᵖ)
    (s : Fin n → (SheafOfModules.free (R := Rᵣ) (ULift.{u} (Fin n))).val.obj X) :
    (exteriorTopFreeHom R n).val.app X
        ((exteriorPowerMk R _ n).app X s) = (freeFinSectionsBasis R n X).det s :=
  exteriorPowerDesc_mk R _ _ n (exteriorTopFreeDeterminant R n) X s

/-- The original wedge of original free sections is a global compatible section. -/
def exteriorTopFreeGenerator (n : ℕ) :
    (exteriorPower R (SheafOfModules.free (R := Rᵣ) (ULift.{u} (Fin n))) n).sections :=
  PresheafOfModules.sectionsMk
    (fun X => (exteriorPowerMk R _ n).app X (freeFinSectionsBasis R n X)) (by
      intro X Y f
      refine (exteriorPowerMk_naturality R _ n f (freeFinSectionsBasis R n X)).trans ?_
      apply congrArg ((exteriorPowerMk R _ n).app Y)
      funext i
      exact freeFinSectionsBasis_restrict R n f i)

/-- The original structure-module map corresponding to the original top wedge section. -/
def exteriorTopFreeInv (n : ℕ) : SheafOfModules.unit Rᵣ ⟶
    exteriorPower R (SheafOfModules.free (R := Rᵣ) (ULift.{u} (Fin n))) n :=
  (SheafOfModules.unitHomEquiv _).symm (exteriorTopFreeGenerator R n)

/-- The inverse map is exactly scalar multiplication of the original ordered basis wedge. -/
@[simp]
theorem exteriorTopFreeInv_apply (n : ℕ) (X : Cᵒᵖ) (r : R.obj.obj X) :
    (exteriorTopFreeInv R n).val.app X r =
      r • (exteriorPowerMk R _ n).app X (freeFinSectionsBasis R n X) := rfl

/-- The actual top exterior power of the actual finite free sheaf is the structure module. -/
def exteriorTopFreeIso (n : ℕ) :
    exteriorPower R (SheafOfModules.free (R := Rᵣ) (ULift.{u} (Fin n))) n ≅
      SheafOfModules.unit Rᵣ where
  hom := exteriorTopFreeHom R n
  inv := exteriorTopFreeInv R n
  hom_inv_id := by
    apply exteriorPower_hom_ext R _ _ n
    intro X s
    change (exteriorTopFreeInv R n).val.app X
        ((exteriorTopFreeHom R n).val.app X ((exteriorPowerMk R _ n).app X s)) =
      (exteriorPowerMk R _ n).app X s
    rw [exteriorTopFreeHom_mk, exteriorTopFreeInv_apply]
    let L := _root_.exteriorPower.alternatingMapLinearEquiv (R := R.obj.obj X)
      ((exteriorPowerMk R (SheafOfModules.free (R := Rᵣ) (ULift.{u} (Fin n))) n).app X)
    have Hb : L (_root_.exteriorPower.ιMulti (R.obj.obj X) n (freeFinSectionsBasis R n X)) =
        (exteriorPowerMk R _ n).app X (freeFinSectionsBasis R n X) :=
      _root_.exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _
    have Hs : L (_root_.exteriorPower.ιMulti (R.obj.obj X) n s) =
        (exteriorPowerMk R _ n).app X s :=
      _root_.exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _
    have H := congrArg L (_root_.exteriorPower.ιMulti_eq_det_smul
      (freeFinSectionsBasis R n X) s)
    rw [map_smul, Hb, Hs] at H
    exact H.symm
  inv_hom_id := by
    apply (SheafOfModules.unitHomEquiv (SheafOfModules.unit Rᵣ)).injective
    apply PresheafOfModules.sections_ext
    intro X
    change (exteriorTopFreeHom R n).val.app X
      ((exteriorTopFreeInv R n).val.app X (1 : R.obj.obj X)) = (1 : R.obj.obj X)
    rw [exteriorTopFreeInv_apply, one_smul, exteriorTopFreeHom_mk]
    exact (freeFinSectionsBasis R n X).det_self

/-- The forward isomorphism is the original universal determinant map. -/
theorem exteriorTopFreeIso_hom (n : ℕ) :
    (exteriorTopFreeIso R n).hom = exteriorTopFreeHom R n := rfl

/-- The inverse isomorphism is the original unit-Hom image of the original wedge section. -/
theorem exteriorTopFreeIso_inv (n : ℕ) :
    (exteriorTopFreeIso R n).inv = exteriorTopFreeInv R n := rfl

end SheafOfModulesOfCommRing
