/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Sheafification

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/LineTensorAssociator.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general;
source ranges [[1, 139]]. Actual objects, maps and hypotheses are preserved.
-/

/-! # The original sheafified associator for two actual lines

The original presheaf associator and two literal sheafification-unit maps define
the comparison. Chart trivializations prove those maps invertible, and do not
choose a replacement tensor or an objectwise derived model.
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

/-- The original unit on the tensor of two line presheaves is an actual iso after
open restriction to a chart trivializing both original lines. -/
theorem isIso_restricted_twoLineUnit {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (L M : X.Modules)
    (eL : L.restrict j ≅ SheafOfModules.unit U.ringCatSheaf)
    (eM : M.restrict j ≅ SheafOfModules.unit U.ringCatSheaf) :
    IsIso ((PresheafOfModulesOfCommRing.pushforward (restrictionRingHom j).hom).map
      ((SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app
        ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L ⊗
            (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M))) := by
  let A := (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L
  let B := (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M
  let F := PresheafOfModulesOfCommRing.pushforward (restrictionRingHom j).hom
  let e : F.obj (A ⊗ B) ≅ (SheafOfModulesOfCommRing.toPresheaf U.sheaf).obj
      (SheafOfModules.unit U.ringCatSheaf) :=
    (PresheafOfModulesOfCommRing.pushforwardTensorIso (restrictionRingHom j).hom A B).symm ≪≫
      tensorIso ((SheafOfModulesOfCommRing.toPresheaf U.sheaf).mapIso eL)
          ((SheafOfModulesOfCommRing.toPresheaf U.sheaf).mapIso eM) ≪≫
      (λ_ ((SheafOfModulesOfCommRing.toPresheaf U.sheaf).obj (SheafOfModules.unit U.ringCatSheaf)))
  exact isIso_restricted_unit_of_iso_sheaf j (A ⊗ B)
    (SheafOfModules.unit U.ringCatSheaf) e

/-- Tensoring the original two-line unit on its right with arbitrary presheaf
coefficients remains invertible after original sheafification. -/
theorem isIso_twoLineUnit_tensor_sheafification {X : Scheme.{u}} (L M : X.Modules)
    {ι : Type v} (Y : ι → Scheme.{u}) (j : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (hc : ∀ x : X, ∃ i y, j i y = x)
    (eL : ∀ i, L.restrict (j i) ≅ SheafOfModules.unit (Y i).ringCatSheaf)
    (eM : ∀ i, M.restrict (j i) ≅ SheafOfModules.unit (Y i).ringCatSheaf)
    (P : PresheafOfModulesOfCommRing.{u} X.sheaf.obj) :
    IsIso ((SheafOfModulesOfCommRing.associatedSheaf X.sheaf).map
      (((SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app
        ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L ⊗
            (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M)) ⊗ₘ 𝟙 P)) := by
  apply isIso_of_restrict_openCover Y j hc
  intro i
  let F := PresheafOfModulesOfCommRing.pushforward (restrictionRingHom (j i)).hom
  let S := SheafOfModulesOfCommRing.associatedSheaf (Y i).sheaf
  let A := (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L ⊗
      (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M
  let η := (SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app A
  have hη : IsIso (F.map η) := isIso_restricted_twoLineUnit (j i) L M (eL i) (eM i)
  have hn := PresheafOfModulesOfCommRing.pushforwardTensorHom_naturality
    (restrictionRingHom (j i)).hom η (𝟙 P)
  simp only [CategoryTheory.Functor.map_id] at hn
  change (F.map η ⊗ₘ 𝟙 (F.obj P)) ≫
      (PresheafOfModulesOfCommRing.pushforwardTensorIso
        (restrictionRingHom (j i)).hom
        ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj
            ((SheafOfModulesOfCommRing.associatedSheaf X.sheaf).obj A)) P).hom =
    (PresheafOfModulesOfCommRing.pushforwardTensorIso
      (restrictionRingHom (j i)).hom A P).hom ≫ F.map (η ⊗ₘ 𝟙 P) at hn
  have hcomp : IsIso ((PresheafOfModulesOfCommRing.pushforwardTensorIso
      (restrictionRingHom (j i)).hom A P).hom ≫ F.map (η ⊗ₘ 𝟙 P)) := by
    rw [← hn]
    infer_instance
  have hg : IsIso (F.map (η ⊗ₘ 𝟙 P)) := by
    rw [← isIso_comp_left_iff
      (PresheafOfModulesOfCommRing.pushforwardTensorIso
        (restrictionRingHom (j i)).hom A P).hom]
    exact hcomp
  have hS : IsIso (S.map (F.map (η ⊗ₘ 𝟙 P))) := inferInstance
  exact (NatIso.isIso_map_iff (restrictionSheafificationIso (j i))
    (η ⊗ₘ 𝟙 P)).mp hS

/-- The literal original left nested-tensor sheafification-unit comparison. -/
def lineTensorLeftUnitComparison (X : Scheme.{u}) (L M : X.Modules) :
    SheafOfModulesOfCommRing.toPresheaf X.sheaf ⋙ tensorLeft
        ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M) ⋙
        tensorLeft ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L) ⋙
            SheafOfModulesOfCommRing.associatedSheaf X.sheaf ⟶
      moduleTensorLeftFunctor X M ⋙ moduleTensorLeftFunctor X L :=
  whiskerRight
    (whiskerLeft (SheafOfModulesOfCommRing.toPresheaf X.sheaf ⋙ tensorLeft
        ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M))
      (SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf))
    (tensorLeft ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L) ⋙
        SheafOfModulesOfCommRing.associatedSheaf X.sheaf)

/-- The literal original right nested-tensor sheafification-unit comparison. -/
def lineTensorRightUnitComparison (X : Scheme.{u}) (L M : X.Modules) :
    SheafOfModulesOfCommRing.toPresheaf X.sheaf ⋙
        tensorLeft ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L ⊗
            (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M) ⋙
          SheafOfModulesOfCommRing.associatedSheaf X.sheaf ⟶
      moduleTensorLeftFunctor X ((moduleTensorLeftFunctor X L).obj M) :=
  whiskerLeft (SheafOfModulesOfCommRing.toPresheaf X.sheaf)
    (whiskerRight ((curriedTensor _).map
      ((SheafOfModulesOfCommRing.associatedSheafUnit X.sheaf).app
        ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L ⊗
            (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M)))
      (SheafOfModulesOfCommRing.associatedSheaf X.sheaf))

/-- The original presheaf associator followed by original module-sheafification. -/
def lineTensorPresheafAssociator (X : Scheme.{u}) (L M : X.Modules) :
    SheafOfModulesOfCommRing.toPresheaf X.sheaf ⋙
        tensorLeft ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L ⊗
            (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M) ⋙
          SheafOfModulesOfCommRing.associatedSheaf X.sheaf ≅
      SheafOfModulesOfCommRing.toPresheaf X.sheaf ⋙ tensorLeft
          ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M) ⋙
        tensorLeft ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L) ⋙
            SheafOfModulesOfCommRing.associatedSheaf X.sheaf :=
  isoWhiskerLeft (SheafOfModulesOfCommRing.toPresheaf X.sheaf)
    (isoWhiskerRight
      (tensorLeftTensor ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj L)
          ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M))
      (SheafOfModulesOfCommRing.associatedSheaf X.sheaf))

/-- The actual original sheafified associator with two line factors. Charts only
prove invertibility of the prescribed unit maps; the maps retain original associator and units. -/
def moduleLineTensorAssociator {X : Scheme.{u}} (L M : X.Modules)
    {ι : Type v} (Y : ι → Scheme.{u}) (j : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (j i)] (hc : ∀ x : X, ∃ i y, j i y = x)
    (eL : ∀ i, L.restrict (j i) ≅ SheafOfModules.unit (Y i).ringCatSheaf)
    (eM : ∀ i, M.restrict (j i) ≅ SheafOfModules.unit (Y i).ringCatSheaf) :
    moduleTensorLeftFunctor X M ⋙ moduleTensorLeftFunctor X L ≅
      moduleTensorLeftFunctor X ((moduleTensorLeftFunctor X L).obj M) := by
  have hleft : IsIso (lineTensorLeftUnitComparison X L M) := by
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro E
    exact isIso_line_tensor_sheafificationUnit L Y j hc eL
      ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M ⊗
          (SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj E)
  have hright : IsIso (lineTensorRightUnitComparison X L M) := by
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro E
    exact isIso_twoLineUnit_tensor_sheafification L M Y j hc eL eM
      ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj E)
  exact (asIso (lineTensorLeftUnitComparison X L M)).symm ≪≫
    (lineTensorPresheafAssociator X L M).symm ≪≫
    asIso (lineTensorRightUnitComparison X L M)
end AlgebraicGeometry.Scheme.Modules
