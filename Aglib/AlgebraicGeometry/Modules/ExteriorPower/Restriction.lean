/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ExteriorPower.Basic
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
# Exterior powers and open restriction

The scheme exterior power is definitionally the generic sheafified exterior
power. Its comparison with restriction to an open uses the original
restriction/sheafification isomorphism, and preserves the original wedge.
No local freeness, finiteness, or condition on the base scheme is imposed.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable (X : Scheme.{u})

/-- The original generic exterior-power functor, specialized to structure modules. -/
abbrev moduleExteriorPowerFunctor (n : ℕ) : X.Modules ⥤ X.Modules :=
  SheafOfModulesOfCommRing.exteriorPowerFunctor X.sheaf n

/-- The original sheafified exterior power of a scheme module. -/
abbrev moduleExteriorPower (M : X.Modules) (n : ℕ) : X.Modules :=
  SheafOfModulesOfCommRing.exteriorPower X.sheaf M n

/-- Restricting the original pointwise exterior presheaf does not change its wedges. -/
def moduleExteriorPresheafOverIso (M : X.Modules) (n : ℕ) (U : X.Opens) :
    (PresheafOfModules.Restriction.restrictPresheaf X.ringCatSheaf U).obj
      (PresheafOfModulesOfCommRing.exteriorPower M.val n) ≅
      PresheafOfModulesOfCommRing.exteriorPower
        (R := (Over.forget U).op ⋙ X.presheaf) (M.over U).val n :=
  PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intros; rfl)

/-- The canonical comparison is the original restriction/sheafification comparison. -/
def moduleExteriorPowerOverIso (M : X.Modules) (n : ℕ) (U : X.Opens) :
    SheafOfModulesOfCommRing.exteriorPower (X.sheaf.over U) (M.over U) n ≅
      (moduleExteriorPower X M n).over U :=
  (PresheafOfModules.sheafification (𝟙 (X.ringCatSheaf.over U).obj)).mapIso
      (moduleExteriorPresheafOverIso X M n U).symm ≪≫
    PresheafOfModules.Restriction.sheafificationOverIso X.ringCatSheaf U _

/-- The restriction/sheafification comparison is the adjunct of the original restricted unit. -/
theorem moduleSheafificationOverIso_hom (U : X.Opens)
    (P : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :
    (PresheafOfModules.Restriction.sheafificationOverIso X.ringCatSheaf U P).hom =
      ((PresheafOfModules.sheafificationAdjunction
        (𝟙 (X.ringCatSheaf.over U).obj)).homEquiv
          ((PresheafOfModules.Restriction.restrictPresheaf X.ringCatSheaf U).obj P)
          (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P).over U)).symm
        (PresheafOfModules.Restriction.restrictedSheafificationUnit X.ringCatSheaf U P) := by
  rw [Adjunction.homEquiv_counit]
  rfl

/-- The comparison sends each original restricted wedge to the same original global wedge. -/
@[simp]
theorem moduleExteriorPowerOverIso_hom_mk (M : X.Modules) (n : ℕ) (U : X.Opens)
    (V : (Over U)ᵒᵖ) (s : Fin n → (M.over U).val.obj V) :
    (moduleExteriorPowerOverIso X M n U).hom.val.app V
        ((SheafOfModulesOfCommRing.exteriorPowerMk
          (X.sheaf.over U) (M.over U) n).app V s) =
      (SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf M n).app
        ((Over.forget U).op.obj V) s := by
  let A := PresheafOfModules.sheafificationAdjunction
    (𝟙 (X.ringCatSheaf.over U).obj)
  let P := PresheafOfModulesOfCommRing.exteriorPower M.val n
  let e := moduleExteriorPresheafOverIso X M n U
  let f := PresheafOfModules.Restriction.restrictedSheafificationUnit X.ringCatSheaf U P
  have H := (A.homEquiv
    (PresheafOfModulesOfCommRing.exteriorPower
      (R := (X.sheaf.over U).obj) (M.over U).val n)
    ((moduleExteriorPower X M n).over U)).apply_symm_apply (e.inv ≫ f)
  rw [Adjunction.homEquiv_counit] at H
  simp only [Functor.map_comp, Category.assoc] at H
  change A.homEquiv _ _
    ((moduleExteriorPowerOverIso X M n U).hom) = e.inv ≫ f at H
  have H' := congrArg (fun φ => φ.app V
    (ModuleCat.exteriorPower.mk
      (R := (X.sheaf.over U).obj.obj V) (M := (M.over U).val.obj V) s)) H
  exact H'

/-- The inverse comparison also preserves the same original wedge. -/
@[simp]
theorem moduleExteriorPowerOverIso_inv_mk (M : X.Modules) (n : ℕ) (U : X.Opens)
    (V : (Over U)ᵒᵖ) (s : Fin n → (M.over U).val.obj V) :
    (moduleExteriorPowerOverIso X M n U).inv.val.app V
        ((SheafOfModulesOfCommRing.exteriorPowerMk X.sheaf M n).app
          ((Over.forget U).op.obj V) s) =
      (SheafOfModulesOfCommRing.exteriorPowerMk
        (X.sheaf.over U) (M.over U) n).app V s := by
  rw [← moduleExteriorPowerOverIso_hom_mk X M n U V s]
  exact ConcreteCategory.congr_hom
    (congrArg (fun φ => φ.val.app V) (moduleExteriorPowerOverIso X M n U).hom_inv_id) _

/-- The restriction comparison is natural for the original coefficient morphisms. -/
theorem moduleExteriorPowerOverIso_naturality {M N : X.Modules} (φ : M ⟶ N)
    (n : ℕ) (U : X.Opens) :
    (SheafOfModulesOfCommRing.exteriorPowerFunctor (X.sheaf.over U) n).map (φ.over U) ≫
        (moduleExteriorPowerOverIso X N n U).hom =
      (moduleExteriorPowerOverIso X M n U).hom ≫
        ((moduleExteriorPowerFunctor X n).map φ).over U := by
  apply SheafOfModulesOfCommRing.exteriorPower_hom_ext
    (X.sheaf.over U) (M.over U) ((moduleExteriorPower X N n).over U) n
  intro V s
  change (moduleExteriorPowerOverIso X N n U).hom.val.app V
      (((SheafOfModulesOfCommRing.exteriorPowerFunctor (X.sheaf.over U) n).map
        (φ.over U)).val.app V
        ((SheafOfModulesOfCommRing.exteriorPowerMk
          (X.sheaf.over U) (M.over U) n).app V s)) =
    (((moduleExteriorPowerFunctor X n).map φ).over U).val.app V
      ((moduleExteriorPowerOverIso X M n U).hom.val.app V
        ((SheafOfModulesOfCommRing.exteriorPowerMk
          (X.sheaf.over U) (M.over U) n).app V s))
  exact (congrArg ((moduleExteriorPowerOverIso X N n U).hom.val.app V)
    (SheafOfModulesOfCommRing.exteriorPowerFunctor_map_mk
      (X.sheaf.over U) (φ.over U) n V s)).trans
    ((moduleExteriorPowerOverIso_hom_mk X N n U V
      (fun i => (φ.over U).val.app V (s i))).trans
      ((SheafOfModulesOfCommRing.exteriorPowerFunctor_map_mk X.sheaf φ n
        ((Over.forget U).op.obj V) s).symm.trans
        (congrArg ((((moduleExteriorPowerFunctor X n).map φ).over U).val.app V)
          (moduleExteriorPowerOverIso_hom_mk X M n U V s)).symm))

end AlgebraicGeometry.Scheme.Modules
