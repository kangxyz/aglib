/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.CategoryTheory.Equivalence

/-!
# Module presheaves over the actual constant ring presheaf

A presheaf of modules over a constant ring is pointwise the original
module-valued presheaf. The two actual functors keep section modules,
restriction functions and coefficient functions. Their unit and counit have
identity components on the original section modules.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.TorsionZMod.Ringed

universe u v r w

variable {C : Type u} [Category.{v} C] (R : Type r) [Ring R]

/-- Ordinary module-valued presheaves as actual presheaves over the constant ring. -/
def toConstantModules : (Cᵒᵖ ⥤ ModuleCat.{w} R) ⥤
    PresheafOfModules.{w} ((Functor.const Cᵒᵖ).obj (RingCat.of R)) where
  obj P := {
    obj X := P.obj X
    map f := P.map f ≫ (ModuleCat.restrictScalarsId R).inv.app _
    map_id X := by
      ext x
      exact ConcreteCategory.congr_hom (P.map_id X) x
    map_comp f g := by
      ext x
      exact ConcreteCategory.congr_hom (P.map_comp f g) x }
  map f := {
    app X := f.app X
    naturality g := by
      ext x
      exact ConcreteCategory.congr_hom (f.naturality g) x }
  map_id P := by ext X x; rfl
  map_comp f g := by ext X x; rfl

/-- Presheaves over the actual constant ring as ordinary module-valued presheaves. -/
def fromConstantModules :
    PresheafOfModules.{w} ((Functor.const Cᵒᵖ).obj (RingCat.of R)) ⥤
      (Cᵒᵖ ⥤ ModuleCat.{w} R) where
  obj M := {
    obj X := M.obj X
    map {X Y} f := ModuleCat.ofHom (X := M.obj X) (Y := M.obj Y) {
      toFun := fun x => M.map f x
      map_add' := fun x y => map_add (M.map f).hom x y
      map_smul' := fun r x => M.map_smul f r x }
    map_id X := by
      ext x
      exact ConcreteCategory.congr_hom (M.map_id X) x
    map_comp f g := by
      ext x
      exact M.map_comp_apply f g x }
  map f := {
    app X := f.app X
    naturality := by
      intro X Y g
      ext x
      exact PresheafOfModules.naturality_apply f g x }
  map_id P := by ext X x; rfl
  map_comp f g := by ext X x; rfl

/-- The actual unit component is the identity linear map on the original section module. -/
def constantPresheafUnitComponent (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (X : Cᵒᵖ) :
    P.obj X ≅ ((toConstantModules R ⋙ fromConstantModules R).obj P).obj X where
  hom := ModuleCat.ofHom {
    toFun := fun x => x
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  inv := ModuleCat.ofHom {
    toFun := fun x => x
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  hom_inv_id := by ext x; rfl
  inv_hom_id := by ext x; rfl

/-- The actual counit component is the identity on the original constant-ring section module. -/
def constantPresheafCounitComponent
    (M : PresheafOfModules.{w} ((Functor.const Cᵒᵖ).obj (RingCat.of R))) (X : Cᵒᵖ) :
    ((fromConstantModules R ⋙ toConstantModules R).obj M).obj X ≅ M.obj X where
  hom := ModuleCat.ofHom {
    toFun := fun x => x
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  inv := ModuleCat.ofHom {
    toFun := fun x => x
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  hom_inv_id := by ext x; rfl
  inv_hom_id := by ext x; rfl

/-- The literal pointwise equivalence over the actual constant ring presheaf. -/
def constantPresheafEquivalence : (Cᵒᵖ ⥤ ModuleCat.{w} R) ≌
    PresheafOfModules.{w} ((Functor.const Cᵒᵖ).obj (RingCat.of R)) where
  functor := toConstantModules R
  inverse := fromConstantModules R
  unitIso := NatIso.ofComponents (fun P =>
    NatIso.ofComponents (constantPresheafUnitComponent R P) (by intros; ext x; rfl))
      (by intros; ext X x; rfl)
  counitIso := NatIso.ofComponents (fun M =>
    PresheafOfModules.isoMk (constantPresheafCounitComponent R M) (by intros; ext x; rfl))
      (by intros; ext X x; rfl)
  functor_unitIso_comp P := by ext X x; rfl

/-- The original underlying abelian presheaf is unchanged by constant-ring conversion. -/
def toConstantModulesUnderlyingIso : toConstantModules (C := C) R ⋙
    PresheafOfModules.toPresheaf _ ≅
      (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{w} R) AddCommGrpCat.{w}).obj
        (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) :=
  NatIso.ofComponents (fun P =>
    NatIso.ofComponents (fun X => Iso.refl (AddCommGrpCat.of (P.obj X)))
      (by intros; ext x; rfl))
      (by intros; ext X x; rfl)

/-- The inverse comparison is the typed identity additive map on the original sections. -/
def fromConstantModulesUnderlyingComponent
    (M : PresheafOfModules.{w} ((Functor.const Cᵒᵖ).obj (RingCat.of R))) (X : Cᵒᵖ) :
    (((fromConstantModules R).obj M) ⋙
      forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}).obj X ≅ M.presheaf.obj X where
  hom := AddCommGrpCat.ofHom {
    toFun := fun x => x
    map_zero' := rfl
    map_add' := by intros; rfl }
  inv := AddCommGrpCat.ofHom {
    toFun := fun x => x
    map_zero' := rfl
    map_add' := by intros; rfl }
  hom_inv_id := by ext x; rfl
  inv_hom_id := by ext x; rfl

/-- The inverse conversion retains that same original underlying abelian presheaf. -/
def fromConstantModulesUnderlyingIso : fromConstantModules (C := C) R ⋙
      (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{w} R) AddCommGrpCat.{w}).obj
        (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) ≅ PresheafOfModules.toPresheaf _ :=
  NatIso.ofComponents (fun M =>
    NatIso.ofComponents (fromConstantModulesUnderlyingComponent R M)
      (by intros; ext x; rfl))
      (by intros; ext X x; rfl)

end CategoryTheory.TorsionZMod.Ringed
