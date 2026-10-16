/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Basic
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.AlgebraicGeometry.Modules.Restriction.Sheafification
public import Aglib.Algebra.Category.ModuleCat.Sheaf.TensorPushforward

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/TensorRestriction.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 67]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# Tensor and actual open restriction

The original inverse section-ring maps of an open immersion specialize the generic tensor
pushforward comparison. This provides a natural isomorphism for arbitrary module sheaves.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry SheafOfModulesOfCommRing
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
variable {X Y : Scheme.{u}} (j : X ⟶ Y) [IsOpenImmersion j]
/-- The original sheaf tensor commutes with actual open restriction. -/
def tensorRestrictionIso (M N : Y.Modules) :
    (moduleTensorLeftFunctor X (M.restrict j)).obj (N.restrict j) ≅
      ((moduleTensorLeftFunctor Y M).obj N).restrict j :=
  SheafOfModulesOfCommRing.tensorPushforwardIso (restrictionRingHom j) M N
/-- Restriction and tensoring commute naturally in the original module argument. -/
def tensorRestrictionNatIso (M : Y.Modules) :
    Scheme.Modules.restrictFunctor j ⋙ moduleTensorLeftFunctor X (M.restrict j) ≅
      moduleTensorLeftFunctor Y M ⋙ Scheme.Modules.restrictFunctor j :=
  NatIso.ofComponents (tensorRestrictionIso j M) (fun {N N'} g => by
    have h := tensorPushforwardIso_naturality (restrictionRingHom j)
      (𝟙 (show SheafOfModulesOfCommRing.{u} Y.sheaf from M)) g
    change (SheafOfModulesOfCommRing.associatedSheaf X.sheaf).map
      (𝟙 ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj (M.restrict j)) ⊗ₘ
        (SheafOfModulesOfCommRing.toPresheaf X.sheaf).map ((Scheme.Modules.restrictFunctor
            j).map g)) ≫ _ =
      _ ≫ (Scheme.Modules.restrictFunctor j).map ((SheafOfModulesOfCommRing.associatedSheaf
          Y.sheaf).map
        (𝟙 ((SheafOfModulesOfCommRing.toPresheaf Y.sheaf).obj M) ⊗ₘ
            (SheafOfModulesOfCommRing.toPresheaf Y.sheaf).map g)) at h
    exact h)
/-- The original open restriction comparison preserves the literal sheafification-unit square. -/
theorem tensorRestrictionIso_unit (M N : Y.Modules) :
    (SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app
        (((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj (M.restrict j)) ⊗
          ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj (N.restrict j))) ≫
      (SheafOfModulesOfCommRing.toPresheaf X.sheaf).map (tensorRestrictionIso j M N).hom =
    PresheafOfModulesOfCommRing.pushforwardTensorHom (restrictionRingHom j).hom
        ((SheafOfModulesOfCommRing.toPresheaf Y.sheaf).obj M)
            ((SheafOfModulesOfCommRing.toPresheaf Y.sheaf).obj N) ≫
      (PresheafOfModulesOfCommRing.pushforward (restrictionRingHom j).hom).map
        ((SheafOfModulesOfCommRing.associatedSheafUnit Y.sheaf).app
          (((SheafOfModulesOfCommRing.toPresheaf Y.sheaf).obj M) ⊗
              ((SheafOfModulesOfCommRing.toPresheaf Y.sheaf).obj N))) :=
  SheafOfModulesOfCommRing.tensorPushforwardIso_unit (restrictionRingHom j) M N
end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
open Opposite TopologicalSpace
variable (X : Scheme.{u})

/-- The sectionwise tensor comparison on the site over an open. -/
def tensorPresheafOverIso (M N : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens) :
    (_root_.PresheafOfModules.Restriction.restrictPresheaf X.ringCatSheaf U).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val) ≅
    PresheafOfModulesOfCommRing.Monoidal.tensorObj
      (R := (Over.forget U).op ⋙ X.presheaf) (M.over U).val (N.over U).val :=
  _root_.PresheafOfModules.isoMk (fun _ => Iso.refl _) (by intros; rfl)

/-- Tensor two supplied unit trivializations on the same open. -/
def tensorOverTrivialization (M N : SheafOfModules.{u} X.ringCatSheaf) (U : X.Opens)
    (e : M.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U))
    (f : N.over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U)) :
    (tensorSheaf X M N).over U ≅ SheafOfModules.unit (X.ringCatSheaf.over U) := by
  let S := _root_.PresheafOfModules.sheafification (𝟙 (X.ringCatSheaf.over U).obj)
  let e' := (SheafOfModules.forget (X.ringCatSheaf.over U)).mapIso e
  let f' := (SheafOfModules.forget (X.ringCatSheaf.over U)).mapIso f
  let t := CategoryTheory.MonoidalCategory.tensorIso
    (C := PresheafOfModulesOfCommRing.{u} ((Over.forget U).op ⋙ X.presheaf)) e' f'
  let l := CategoryTheory.MonoidalCategory.leftUnitor
    (C := PresheafOfModulesOfCommRing.{u} ((Over.forget U).op ⋙ X.presheaf))
    (SheafOfModules.unit (X.ringCatSheaf.over U)).val
  exact (_root_.PresheafOfModules.Restriction.sheafificationOverIso X.ringCatSheaf U _).symm ≪≫
    S.mapIso (tensorPresheafOverIso X M N U) ≪≫ S.mapIso t ≪≫ S.mapIso l ≪≫
    asIso
      ((_root_.PresheafOfModules.sheafificationAdjunction
        (𝟙 (X.ringCatSheaf.over U).obj)).counit.app
      (SheafOfModules.unit (X.ringCatSheaf.over U)))

end AlgebraicGeometry.Scheme.Modules
