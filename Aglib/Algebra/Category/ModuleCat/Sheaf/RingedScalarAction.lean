/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aglib contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-! # Actual scalar sections act on underlying native ringed module sheaves

A compatible family of scalar sections acts additively on each original
section group. Noncentral left multiplication is not asserted module-linear.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory
namespace SheafOfModules
universe u v r w
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{r}) {Λ : Type r} [Ring Λ]
  (ι : (Functor.const Cᵒᵖ).obj (RingCat.of Λ) ⟶ R.obj)

/-- Original left multiplication through the supplied compatible scalar sections. -/
def underlyingScalarSection (a : Λ) : toSheaf.{w} R ⟶ toSheaf.{w} R where
  app M := {
    hom := {
      app U := AddCommGrpCat.ofHom {
        toFun := fun x => (ι.app U a) • (show M.val.obj U from x)
        map_zero' := smul_zero _
        map_add' := smul_add _ }
      naturality {U V} f := by
        ext x
        let y : M.val.obj U := x
        change (ι.app V a) • (show M.val.obj V from M.val.map f y) =
          M.val.map f ((ι.app U a) • y)
        rw [M.val.map_smul]
        have h : R.obj.map f (ι.app U a) = ι.app V a :=
          (ConcreteCategory.congr_hom (ι.naturality f) a).symm
        rw [h] } }
  naturality {M N} f := by
    ext U x
    exact ((f.val.app U).hom.map_smul (ι.app U a) x).symm

/-- The underlying scalar acts on the exact original section group. -/
theorem underlyingScalarSection_apply (a : Λ) (M : SheafOfModules.{w} R)
    (U : Cᵒᵖ) (x : M.val.obj U) :
    (((underlyingScalarSection R ι a).app M).hom.app U) x = ι.app U a • x := rfl

end SheafOfModules
