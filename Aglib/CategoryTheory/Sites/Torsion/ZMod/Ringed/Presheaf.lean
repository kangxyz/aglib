/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.ConstantRing.Presheaf

/-! # Compatibility names for the general constant-ring presheaf equivalence

The implementations live in the arbitrary-ring owner. These declarations
retain the historical public names and literal original section maps.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.TorsionZMod.Ringed

universe u v r w

variable {C : Type u} [Category.{v} C] (R : Type r) [Ring R]

/-- Ordinary module-valued presheaves as actual presheaves over the constant ring. -/
abbrev toConstantModules : (Cᵒᵖ ⥤ ModuleCat.{w} R) ⥤
    PresheafOfModules.{w} ((Functor.const Cᵒᵖ).obj (RingCat.of R)) :=
  ModuleCat.Sheaf.ConstantRing.toConstantModules (C := C) R

/-- Presheaves over the actual constant ring as ordinary module-valued presheaves. -/
abbrev fromConstantModules :
    PresheafOfModules.{w} ((Functor.const Cᵒᵖ).obj (RingCat.of R)) ⥤
      (Cᵒᵖ ⥤ ModuleCat.{w} R) :=
  ModuleCat.Sheaf.ConstantRing.fromConstantModules (C := C) R

/-- The actual unit component is the identity linear map on the original section module. -/
abbrev constantPresheafUnitComponent (P : Cᵒᵖ ⥤ ModuleCat.{w} R) (X : Cᵒᵖ) :
    P.obj X ≅ ((toConstantModules R ⋙ fromConstantModules R).obj P).obj X :=
  ModuleCat.Sheaf.ConstantRing.constantPresheafUnitComponent R P X

/-- The actual counit component is the identity on the original constant-ring section module. -/
abbrev constantPresheafCounitComponent
    (M : PresheafOfModules.{w} ((Functor.const Cᵒᵖ).obj (RingCat.of R))) (X : Cᵒᵖ) :
    ((fromConstantModules R ⋙ toConstantModules R).obj M).obj X ≅ M.obj X :=
  ModuleCat.Sheaf.ConstantRing.constantPresheafCounitComponent R M X

/-- The literal pointwise equivalence over the actual constant ring presheaf. -/
abbrev constantPresheafEquivalence : (Cᵒᵖ ⥤ ModuleCat.{w} R) ≌
    PresheafOfModules.{w} ((Functor.const Cᵒᵖ).obj (RingCat.of R)) :=
  ModuleCat.Sheaf.ConstantRing.constantPresheafEquivalence (C := C) R

/-- The original underlying abelian presheaf is unchanged by constant-ring conversion. -/
abbrev toConstantModulesUnderlyingIso : toConstantModules (C := C) R ⋙
    PresheafOfModules.toPresheaf _ ≅
      (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{w} R) AddCommGrpCat.{w}).obj
        (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) :=
  ModuleCat.Sheaf.ConstantRing.toConstantModulesUnderlyingIso (C := C) R

/-- The inverse comparison is the typed identity additive map on the original sections. -/
abbrev fromConstantModulesUnderlyingComponent
    (M : PresheafOfModules.{w} ((Functor.const Cᵒᵖ).obj (RingCat.of R))) (X : Cᵒᵖ) :
    (((fromConstantModules R).obj M) ⋙
      forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}).obj X ≅ M.presheaf.obj X :=
  ModuleCat.Sheaf.ConstantRing.fromConstantModulesUnderlyingComponent R M X

/-- The inverse conversion retains that same original underlying abelian presheaf. -/
abbrev fromConstantModulesUnderlyingIso : fromConstantModules (C := C) R ⋙
      (Functor.whiskeringRight Cᵒᵖ (ModuleCat.{w} R) AddCommGrpCat.{w}).obj
        (forget₂ (ModuleCat.{w} R) AddCommGrpCat.{w}) ≅ PresheafOfModules.toPresheaf _ :=
  ModuleCat.Sheaf.ConstantRing.fromConstantModulesUnderlyingIso (C := C) R

end CategoryTheory.TorsionZMod.Ringed
