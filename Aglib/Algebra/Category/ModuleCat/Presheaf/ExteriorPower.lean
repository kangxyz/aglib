/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.ExteriorPower.Semilinear
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing

/-!
# The actual exterior power of a presheaf of modules

Over an arbitrary presheaf of commutative rings, take the native module
exterior power at each object. Its restriction is the semilinear exterior
map of the original restriction. The resulting functor retains the literal
wedge restriction and coefficient formulas. Ring, module, category-object
and category-morphism universes remain independent; the exterior carrier
is in the maximum of the ring and module universes.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory

universe u v w w'

namespace PresheafOfModulesOfCommRing

variable {C : Type w} [Category.{w'} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- The restriction of native exterior powers through the original ring and module maps. -/
def exteriorPowerRestriction (M : PresheafOfModulesOfCommRing.{v} R) (n : ℕ)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    (M.obj X).exteriorPower n ⟶
      (ModuleCat.restrictScalars (R.map f).hom).obj ((M.obj Y).exteriorPower n) :=
  ModuleCat.semilinearMapAddEquiv (R.map f).hom _ _
    (_root_.exteriorPower.mapSemilinear n (M.restrictₛₗ f))

/-- The actual restriction sends an original wedge to the wedge of original restrictions. -/
@[simp]
theorem exteriorPowerRestriction_mk (M : PresheafOfModulesOfCommRing.{v} R) (n : ℕ)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (s : Fin n → M.obj X) :
    exteriorPowerRestriction M n f
        (ModuleCat.exteriorPower.mk (R := R.obj X) (M := M.obj X) s) =
      ModuleCat.exteriorPower.mk (R := R.obj Y) (M := M.obj Y) (fun i => M.map f (s i)) :=
  _root_.exteriorPower.mapSemilinear_apply_ιMulti
    (R := R.obj X) (S := R.obj Y) n (M.restrictₛₗ f) s

/-- Pointwise native exterior powers, with the original semilinear restriction maps. -/
def exteriorPower (M : PresheafOfModulesOfCommRing.{v} R) (n : ℕ) :
    PresheafOfModulesOfCommRing.{max u v} R :=
  mk (fun X => (M.obj X).exteriorPower n)
    (fun f => exteriorPowerRestriction M n f)
    (fun X => by
      apply ModuleCat.exteriorPower.hom_ext
      apply ModuleCat.AlternatingMap.ext
      intro s
      change exteriorPowerRestriction M n (𝟙 X)
        (ModuleCat.exteriorPower.mk (R := R.obj X) (M := M.obj X) s) = _
      rw [exteriorPowerRestriction_mk]
      simp only [PresheafOfModules.map_id]
      rfl)
    (fun {X Y Z} f g => by
      apply ModuleCat.exteriorPower.hom_ext
      apply ModuleCat.AlternatingMap.ext
      intro s
      change exteriorPowerRestriction M n (f ≫ g)
          (ModuleCat.exteriorPower.mk (R := R.obj X) (M := M.obj X) s) =
        exteriorPowerRestriction M n g
          (exteriorPowerRestriction M n f
            (ModuleCat.exteriorPower.mk (R := R.obj X) (M := M.obj X) s))
      rw [exteriorPowerRestriction_mk M n f s,
        exteriorPowerRestriction_mk M n g,
        exteriorPowerRestriction_mk M n (f ≫ g)]
      apply congrArg (ModuleCat.exteriorPower.mk (R := R.obj Z) (M := M.obj Z))
      funext i
      exact M.map_comp_apply f g (s i))

/-- The exterior presheaf's value is exactly the native module exterior power. -/
@[simp]
theorem exteriorPower_obj (M : PresheafOfModulesOfCommRing.{v} R) (n : ℕ) (X : Cᵒᵖ) :
    (exteriorPower M n).obj X = (M.obj X).exteriorPower n := rfl

/-- The literal wedge formula for the original exterior-presheaf restriction. -/
@[simp]
theorem exteriorPower_map_mk (M : PresheafOfModulesOfCommRing.{v} R) (n : ℕ)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (s : Fin n → M.obj X) :
    (exteriorPower M n).map f
        (ModuleCat.exteriorPower.mk (R := R.obj X) (M := M.obj X) s) =
      ModuleCat.exteriorPower.mk (R := R.obj Y) (M := M.obj Y) (fun i => M.map f (s i)) :=
  exteriorPowerRestriction_mk M n f s

/-- A coefficient morphism acts through its original native exterior maps at every object. -/
def exteriorPowerMap {M N : PresheafOfModulesOfCommRing.{v} R} (φ : M ⟶ N) (n : ℕ) :
    exteriorPower M n ⟶ exteriorPower N n :=
  homMk (fun X => ModuleCat.exteriorPower.map (φ.app' X) n) (by
    intro X Y f
    apply ModuleCat.exteriorPower.hom_ext
    apply ModuleCat.AlternatingMap.ext
    intro s
    change ModuleCat.exteriorPower.map (φ.app' Y) n
        (exteriorPowerRestriction M n f
          (ModuleCat.exteriorPower.mk (R := R.obj X) (M := M.obj X) s)) =
      exteriorPowerRestriction N n f
        (ModuleCat.exteriorPower.map (φ.app' X) n
          (ModuleCat.exteriorPower.mk (R := R.obj X) (M := M.obj X) s))
    rw [exteriorPowerRestriction_mk, ModuleCat.exteriorPower.map_mk,
      ModuleCat.exteriorPower.map_mk, exteriorPowerRestriction_mk]
    apply congrArg (ModuleCat.exteriorPower.mk (R := R.obj Y) (M := N.obj Y))
    funext i
    exact naturality_apply φ f (s i))

/-- The coefficient formula is exactly the wedge of the original component maps. -/
@[simp]
theorem exteriorPowerMap_app_mk {M N : PresheafOfModulesOfCommRing.{v} R}
    (φ : M ⟶ N) (n : ℕ) (X : Cᵒᵖ) (s : Fin n → M.obj X) :
    (exteriorPowerMap φ n).app X
        (ModuleCat.exteriorPower.mk (R := R.obj X) (M := M.obj X) s) =
      ModuleCat.exteriorPower.mk (R := R.obj X) (M := N.obj X) (fun i => φ.app X (s i)) :=
  _root_.exteriorPower.map_apply_ιMulti (R := R.obj X) (φ.app' X).hom s

/-- The original pointwise exterior-power functor on actual module presheaves. -/
def exteriorPowerFunctor (R : Cᵒᵖ ⥤ CommRingCat.{u}) (n : ℕ) :
    PresheafOfModulesOfCommRing.{v} R ⥤ PresheafOfModulesOfCommRing.{max u v} R where
  obj M := exteriorPower M n
  map φ := exteriorPowerMap φ n
  map_id M := by
    ext X : 1
    apply ModuleCat.hom_ext
    exact _root_.exteriorPower.map_id
  map_comp φ ψ := by
    ext X : 1
    apply ModuleCat.hom_ext
    exact _root_.exteriorPower.map_comp _ _

end PresheafOfModulesOfCommRing
