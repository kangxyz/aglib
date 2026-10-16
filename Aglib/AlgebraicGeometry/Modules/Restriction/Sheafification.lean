/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Aglib.Algebra.Category.ModuleCat.Sheaf.SheafificationPushforward
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Tensor.Basic
public import Aglib.Algebra.Category.ModuleCat.Sheaf.TensorPushforward

/-!
# Open restriction and original module-sheafification units

Relocated from `Aglib/AlgebraicGeometry/Modules/Tensor/Restriction.lean` at Aglib
`451aeda6b8bb5b44402b574dd6cf60f912360f8c`,
SHA-256 `62d381bf6fbdf1710df9541aa8958ebad91a32674f13d4e4f3ed3e64f6f7b76b`.
Relocated from `Aglib/AlgebraicGeometry/Modules/Tensor/Sheafification.lean` at Aglib
`451aeda6b8bb5b44402b574dd6cf60f912360f8c`,
SHA-256 `07831bbd73ab7751d7641150adbd9762c61c20115f4dfbe9bef4e597c8f1c32e`.
The statements retain their original universes, hypotheses and actual maps.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
  CategoryTheory.MonoidalCategory AlgebraicGeometry SheafOfModulesOfCommRing
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

section
variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
/-- The actual inverse section-ring maps of an open immersion. -/
def restrictionRingHom : X.sheaf ⟶
    (j.opensFunctor.sheafPushforwardContinuous CommRingCat
      (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y)).obj Y.sheaf :=
  ⟨{ app U := (j.appIso U.unop).inv
     naturality := fun {_ _} f => j.appIso_inv_naturality f }⟩
/-- The original restriction ring morphism is invertible on every open. -/
instance restrictionRingHom_isIso : IsIso (restrictionRingHom j).hom := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro U
  change IsIso (j.appIso U.unop).inv
  infer_instance
end

/-- The original module-sheafification comparison under open restriction. -/
def restrictionSheafificationIso {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :
    PresheafOfModulesOfCommRing.pushforward (restrictionRingHom j).hom ⋙
        SheafOfModulesOfCommRing.associatedSheaf U.sheaf ≅
      SheafOfModulesOfCommRing.associatedSheaf X.sheaf ⋙ Scheme.Modules.restrictFunctor j :=
  SheafOfModules.sheafificationPushforwardIso
    (F := j.opensFunctor) (J := Opens.grothendieckTopology U)
    (K := Opens.grothendieckTopology X)
    (S := U.ringCatSheaf) (R := X.ringCatSheaf)
    ⟨whiskerRight (restrictionRingHom j).hom (forget₂ CommRingCat RingCat)⟩

/-- The sheafified original unit remains invertible after the actual open restriction. -/
theorem isIso_sheafified_restricted_unit {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (P : PresheafOfModulesOfCommRing.{u} X.sheaf.obj) :
    IsIso ((SheafOfModulesOfCommRing.associatedSheaf U.sheaf).map
      ((PresheafOfModulesOfCommRing.pushforward (restrictionRingHom j).hom).map
        ((SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app P))) :=
  SheafOfModules.isIso_sheafification_pushforward_unit
    (F := j.opensFunctor) (J := Opens.grothendieckTopology U)
    (K := Opens.grothendieckTopology X)
    (S := U.ringCatSheaf) (R := X.ringCatSheaf)
    ⟨whiskerRight (restrictionRingHom j).hom (forget₂ CommRingCat RingCat)⟩ P

/-- A presheaf which is an actual module sheaf after open restriction has
an invertible restricted original sheafification unit before further tensoring. -/
theorem isIso_restricted_unit_of_iso_sheaf {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (P : PresheafOfModulesOfCommRing.{u} X.sheaf.obj)
    (M : U.Modules)
    (e : (PresheafOfModulesOfCommRing.pushforward (restrictionRingHom j).hom).obj P ≅
      (SheafOfModulesOfCommRing.toPresheaf U.sheaf).obj M) :
    IsIso ((PresheafOfModulesOfCommRing.pushforward (restrictionRingHom j).hom).map
      ((SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app P)) := by
  let F := PresheafOfModulesOfCommRing.pushforward (restrictionRingHom j).hom
  have hη : IsIso ((SheafOfModulesOfCommRing.associatedSheafUnit U.sheaf).app (F.obj P)) :=
    (PresheafOfModules.sheafificationAdjunction
      (R := U.ringCatSheaf) (𝟙 _)).isIso_unit_app_of_iso e
  have h := SheafOfModules.sheafificationPushforwardComparison_unit
    (F := j.opensFunctor) (J := Opens.grothendieckTopology U)
    (K := Opens.grothendieckTopology X)
    (S := U.ringCatSheaf) (R := X.ringCatSheaf)
    ⟨whiskerRight (restrictionRingHom j).hom (forget₂ CommRingCat RingCat)⟩ P
  change (SheafOfModulesOfCommRing.associatedSheafUnit U.sheaf).app (F.obj P) ≫
      (SheafOfModulesOfCommRing.toPresheaf U.sheaf).map ((restrictionSheafificationIso
          j).hom.app P) =
    F.map ((SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app P) at h
  rw [← h]
  infer_instance

end AlgebraicGeometry.Scheme.Modules
