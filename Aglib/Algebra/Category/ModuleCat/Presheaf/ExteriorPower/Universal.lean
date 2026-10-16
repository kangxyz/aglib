/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Presheaf.ExteriorPower

/-!
# The universal property of actual exterior module presheaves

Compatible families of the original sectionwise alternating maps are
represented by the existing exterior presheaf. The equivalence sends a
morphism to its evaluation on the original wedges; its inverse is the
native exterior-power descent at every object. Compatibility uses the
original coefficient-ring and module restriction maps.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory

universe u v w w'

namespace PresheafOfModulesOfCommRing

variable {C : Type w} [Category.{w'} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Native sectionwise alternating maps compatible with the original restrictions. -/
@[ext]
structure AlternatingMap (M : PresheafOfModulesOfCommRing.{v} R)
    (N : PresheafOfModulesOfCommRing.{max u v} R) (n : ℕ) where
  app (X : Cᵒᵖ) : ModuleCat.AlternatingMap (R := R.obj X) (M.obj X) (N.obj X) n
  naturality {X Y : Cᵒᵖ} (f : X ⟶ Y) (s : Fin n → M.obj X) :
    N.map f (app X s) = app Y (fun i => M.map f (s i))

namespace AlternatingMap

variable {M : PresheafOfModulesOfCommRing.{v} R}
  {N P : PresheafOfModulesOfCommRing.{max u v} R} {n : ℕ}

/-- Postcomposition uses each original coefficient morphism. -/
def postcomp (d : AlternatingMap M N n) (φ : N ⟶ P) : AlternatingMap M P n where
  app X := (d.app X).postcomp (φ.app' X)
  naturality {X Y} f s := by
    change P.map f (φ.app X (d.app X s)) = φ.app Y (d.app Y (fun i => M.map f (s i)))
    exact (naturality_apply φ f (d.app X s)).symm.trans
      (congrArg (fun x : N.obj Y => φ.app' Y x) (d.naturality f s))

/-- The original wedge at every object is a compatible alternating family. -/
def wedge (M : PresheafOfModulesOfCommRing.{v} R) (n : ℕ) :
    AlternatingMap M (exteriorPower M n) n where
  app X := ModuleCat.exteriorPower.mk (R := R.obj X) (M := M.obj X)
  naturality f s := exteriorPower_map_mk M n f s

/-- The unique presheaf map induced by the compatible sectionwise alternating family. -/
def desc (d : AlternatingMap M N n) : exteriorPower M n ⟶ N :=
  homMk (fun X => ModuleCat.exteriorPower.desc (d.app X)) (by
    intro X Y f
    apply ModuleCat.exteriorPower.hom_ext
    apply ModuleCat.AlternatingMap.ext
    intro s
    change ModuleCat.exteriorPower.desc (d.app Y)
        ((exteriorPower M n).map f
          (ModuleCat.exteriorPower.mk (R := R.obj X) (M := M.obj X) s)) =
      N.map f (ModuleCat.exteriorPower.desc (d.app X)
        (ModuleCat.exteriorPower.mk (R := R.obj X) (M := M.obj X) s))
    rw [exteriorPower_map_mk, ModuleCat.exteriorPower.desc_mk,
      ModuleCat.exteriorPower.desc_mk]
    exact (d.naturality f s).symm)

/-- Descent evaluates on a wedge by the given original alternating map. -/
@[simp]
theorem desc_app_mk (d : AlternatingMap M N n) (X : Cᵒᵖ) (s : Fin n → M.obj X) :
    d.desc.app X (ModuleCat.exteriorPower.mk (R := R.obj X) (M := M.obj X) s) =
      d.app X s :=
  ModuleCat.exteriorPower.desc_mk (d.app X) s

end AlternatingMap

/-- Morphisms out of the actual exterior presheaf are exactly compatible alternating families. -/
def exteriorPowerHomEquiv (M : PresheafOfModulesOfCommRing.{v} R)
    (N : PresheafOfModulesOfCommRing.{max u v} R) (n : ℕ) :
    (exteriorPower M n ⟶ N) ≃ AlternatingMap M N n where
  toFun φ := (AlternatingMap.wedge M n).postcomp φ
  invFun d := d.desc
  left_inv φ := by
    ext X : 1
    apply ModuleCat.exteriorPower.hom_ext
    apply ModuleCat.AlternatingMap.ext
    intro s
    exact ModuleCat.exteriorPower.desc_mk _ s
  right_inv d := by
    ext X s
    exact ModuleCat.exteriorPower.desc_mk (d.app X) s

/-- The universal equivalence literally evaluates the original morphism on the original wedge. -/
theorem exteriorPowerHomEquiv_apply (M : PresheafOfModulesOfCommRing.{v} R)
    (N : PresheafOfModulesOfCommRing.{max u v} R) (n : ℕ)
    (φ : exteriorPower M n ⟶ N) (X : Cᵒᵖ) (s : Fin n → M.obj X) :
    (exteriorPowerHomEquiv M N n φ).app X s =
      φ.app X (ModuleCat.exteriorPower.mk (R := R.obj X) (M := M.obj X) s) := rfl

/-- The inverse universal map retains the original pointwise native exterior descent. -/
theorem exteriorPowerHomEquiv_symm_app (M : PresheafOfModulesOfCommRing.{v} R)
    (N : PresheafOfModulesOfCommRing.{max u v} R) (n : ℕ)
    (d : AlternatingMap M N n) (X : Cᵒᵖ) :
    ((exteriorPowerHomEquiv M N n).symm d).app X = ModuleCat.exteriorPower.desc (d.app X) := rfl

end PresheafOfModulesOfCommRing
