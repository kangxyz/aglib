/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Sections

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/ProjectionFormula.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 184]]. Actual objects, maps and hypotheses are preserved.
-/

/-!
# The original projection-formula map

Define the ordinary module-sheaf projection-formula arrow through the original
pullback/pushforward adjunction unit and tensor pushforward map. Prove naturality
in both variables and the actual unit and section formulas.
-/

@[expose] public section
noncomputable section

section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
  SheafOfModulesOfCommRing
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
/-- Canonical ring and module tensor maps for the actual scheme pushforward. -/
def pushforwardRingHom : Y.sheaf ⟶
    ((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous CommRingCat
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X)).obj X.sheaf :=
  ⟨f.c⟩
/-- The original tensor comparison for the actual geometric direct image. -/
def modulePushforwardTensorMap (M N : X.Modules) :
    (moduleTensorLeftFunctor Y ((Scheme.Modules.pushforward f).obj M)).obj
        ((Scheme.Modules.pushforward f).obj N) ⟶
      (Scheme.Modules.pushforward f).obj ((moduleTensorLeftFunctor X M).obj N) :=
  SheafOfModulesOfCommRing.pushforwardTensorMap (pushforwardRingHom f) M N
/-- The original geometric adjunction unit and actual tensor pushforward map
form the ordinary projection-formula arrow. -/
def projectionFormulaMap (E : Y.Modules) (M : X.Modules) :
    (moduleTensorLeftFunctor Y E).obj ((Scheme.Modules.pushforward f).obj M) ⟶
      (Scheme.Modules.pushforward f).obj
        ((moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)).obj M) :=
  (moduleTensorCoefficientMap Y ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E)).app
      ((Scheme.Modules.pushforward f).obj M) ≫
    modulePushforwardTensorMap f ((Scheme.Modules.pullback f).obj E) M
/-- The forward map is literally the original adjunction-unit composite. -/
theorem projectionFormulaMap_eq (E : Y.Modules) (M : X.Modules) :
    projectionFormulaMap f E M =
      (moduleTensorCoefficientMap Y
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E)).app
          ((Scheme.Modules.pushforward f).obj M) ≫
        modulePushforwardTensorMap f ((Scheme.Modules.pullback f).obj E) M := rfl

theorem modulePushforwardTensorMap_naturality {E E' : X.Modules}
    (g : E ⟶ E') (M : X.Modules) :
    (moduleTensorRightFunctor Y ((Scheme.Modules.pushforward f).obj M)).map
        ((Scheme.Modules.pushforward f).map g) ≫ modulePushforwardTensorMap f E' M =
      modulePushforwardTensorMap f E M ≫ (Scheme.Modules.pushforward f).map
        ((moduleTensorRightFunctor X M).map g) := by
  have h := pushforwardTensorMap_naturality (pushforwardRingHom f) g
    (𝟙 (show SheafOfModulesOfCommRing.{u} X.sheaf from M))
  change (SheafOfModulesOfCommRing.associatedSheaf Y.sheaf).map
    ((SheafOfModulesOfCommRing.toPresheaf Y.sheaf).map ((Scheme.Modules.pushforward f).map g) ⊗ₘ
      𝟙 ((SheafOfModulesOfCommRing.toPresheaf Y.sheaf).obj ((Scheme.Modules.pushforward
          f).obj M))) ≫ _ =
    _ ≫ (Scheme.Modules.pushforward f).map ((SheafOfModulesOfCommRing.associatedSheaf X.sheaf).map
      ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).map g ⊗ₘ 𝟙
          ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj M))) at h
  exact h
/-- The ordinary projection-formula arrow is natural in the original coefficient. -/
def projectionFormulaNatTrans (M : X.Modules) :
    moduleTensorRightFunctor Y ((Scheme.Modules.pushforward f).obj M) ⟶
      Scheme.Modules.pullback f ⋙ moduleTensorRightFunctor X M ⋙
        Scheme.Modules.pushforward f where
  app E := projectionFormulaMap f E M
  naturality {E E'} g := by
    let C := moduleTensorRightFunctor Y ((Scheme.Modules.pushforward f).obj M)
    change C.map g ≫ C.map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E') ≫
        modulePushforwardTensorMap f ((Scheme.Modules.pullback f).obj E') M =
      (C.map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E) ≫
        modulePushforwardTensorMap f ((Scheme.Modules.pullback f).obj E) M) ≫ _
    rw [← Category.assoc, ← C.map_comp]
    erw [(Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality g]
    rw [C.map_comp, Category.assoc]
    erw [modulePushforwardTensorMap_naturality f ((Scheme.Modules.pullback f).map g) M]
    rw [Category.assoc]
    rfl
/-- The original adjunction-unit projection formula agrees with the actual unit unitor. -/
theorem projectionFormulaMap_unit (M : X.Modules) :
    projectionFormulaMap f (SheafOfModules.unit Y.ringCatSheaf) M ≫
      (Scheme.Modules.pushforward f).map
        ((moduleTensorRightFunctor X M).map (pullbackUnitIso f).hom ≫
          (SheafOfModulesOfCommRing.tensorLeftUnitIso X.sheaf).hom.app M) =
      (SheafOfModulesOfCommRing.tensorLeftUnitIso Y.sheaf).hom.app
          ((Scheme.Modules.pushforward f).obj M) := by
  let C := moduleTensorRightFunctor Y ((Scheme.Modules.pushforward f).obj M)
  have hu : (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      (SheafOfModules.unit Y.ringCatSheaf) ≫
      (Scheme.Modules.pushforward f).map (pullbackUnitIso f).hom =
        tensorPushforwardUnitMap (pushforwardRingHom f) :=
    SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      f.toRingCatSheafHom
  have hn := modulePushforwardTensorMap_naturality f (pullbackUnitIso f).hom M
  change C.map ((Scheme.Modules.pushforward f).map (pullbackUnitIso f).hom) ≫ _ = _ at hn
  change (C.map ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      (SheafOfModules.unit Y.ringCatSheaf)) ≫ _) ≫ _ = _
  rw [Functor.map_comp, Category.assoc]
  rw [← Category.assoc _ _ ((Scheme.Modules.pushforward f).map
    ((SheafOfModulesOfCommRing.tensorLeftUnitIso X.sheaf).hom.app M))]
  erw [← hn]
  rw [← Category.assoc, ← Category.assoc, ← C.map_comp, hu]
  exact pushforwardTensorMap_leftUnit (pushforwardRingHom f) M
/-- The original direct-image tensor arrow is natural in its second module. -/
theorem modulePushforwardTensorMap_naturality_right (E : X.Modules)
    {M N : X.Modules} (g : M ⟶ N) :
    (moduleTensorLeftFunctor Y ((Scheme.Modules.pushforward f).obj E)).map
        ((Scheme.Modules.pushforward f).map g) ≫ modulePushforwardTensorMap f E N =
      modulePushforwardTensorMap f E M ≫ (Scheme.Modules.pushforward f).map
        ((moduleTensorLeftFunctor X E).map g) := by
  have h := pushforwardTensorMap_naturality (pushforwardRingHom f)
    (𝟙 (show SheafOfModulesOfCommRing.{u} X.sheaf from E)) g
  change (SheafOfModulesOfCommRing.associatedSheaf Y.sheaf).map
    (𝟙 ((SheafOfModulesOfCommRing.toPresheaf Y.sheaf).obj ((Scheme.Modules.pushforward f).obj E)) ⊗ₘ
      (SheafOfModulesOfCommRing.toPresheaf Y.sheaf).map ((Scheme.Modules.pushforward f).map
          g)) ≫ _ =
    _ ≫ (Scheme.Modules.pushforward f).map ((SheafOfModulesOfCommRing.associatedSheaf X.sheaf).map
      (𝟙 ((SheafOfModulesOfCommRing.toPresheaf X.sheaf).obj E) ⊗ₘ
          (SheafOfModulesOfCommRing.toPresheaf X.sheaf).map g)) at h
  exact h
/-- The original projection-formula arrow is natural in the source module. -/
theorem projectionFormulaMap_naturality (E : Y.Modules)
    {M N : X.Modules} (g : M ⟶ N) :
    (moduleTensorLeftFunctor Y E).map ((Scheme.Modules.pushforward f).map g) ≫
        projectionFormulaMap f E N =
      projectionFormulaMap f E M ≫ (Scheme.Modules.pushforward f).map
        ((moduleTensorLeftFunctor X ((Scheme.Modules.pullback f).obj E)).map g) := by
  dsimp only [projectionFormulaMap]
  rw [← Category.assoc]
  erw [(moduleTensorCoefficientMap Y
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E)).naturality
      ((Scheme.Modules.pushforward f).map g)]
  rw [Category.assoc]
  erw [modulePushforwardTensorMap_naturality_right f ((Scheme.Modules.pullback f).obj E) g]
  rw [Category.assoc]
end AlgebraicGeometry.Scheme.Modules
end

section
universe u
open CategoryTheory AlgebraicGeometry Opposite SheafOfModulesOfCommRing
namespace AlgebraicGeometry.Scheme.Modules
/-- The original geometric pushforward tensor arrow preserves the original pure tensor. -/
theorem modulePushforwardTensorMap_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E M : X.Modules) (U : Y.Opens)
    (e : Γ((Scheme.Modules.pushforward f).obj E, U))
    (m : Γ((Scheme.Modules.pushforward f).obj M, U)) :
    (modulePushforwardTensorMap f E M).app U
        (moduleTensorSection Y ((Scheme.Modules.pushforward f).obj E)
          ((Scheme.Modules.pushforward f).obj M) U e m) =
      moduleTensorSection X E M (f ⁻¹ᵁ U) e m :=
  SheafOfModulesOfCommRing.pushforwardTensorMap_tensorSection (pushforwardRingHom f) E M (op U) e m
/-- The original projection-formula map acts by the original geometric adjunction unit. -/
theorem projectionFormulaMap_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    (E : Y.Modules) (M : X.Modules) (U : Y.Opens) (e : Γ(E, U))
    (m : Γ((Scheme.Modules.pushforward f).obj M, U)) :
    (projectionFormulaMap f E M).app U
        (moduleTensorSection Y E ((Scheme.Modules.pushforward f).obj M) U e m) =
      moduleTensorSection X ((Scheme.Modules.pullback f).obj E) M (f ⁻¹ᵁ U)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E).app U e) m := by
  rw [projectionFormulaMap_eq, Scheme.Modules.Hom.comp_app, AddCommGrpCat.comp_apply]
  erw [moduleTensorCoefficientMap_section
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app E)
      ((Scheme.Modules.pushforward f).obj M) U e m]
  exact modulePushforwardTensorMap_section f ((Scheme.Modules.pullback f).obj E) M U _ m
end AlgebraicGeometry.Scheme.Modules
end
