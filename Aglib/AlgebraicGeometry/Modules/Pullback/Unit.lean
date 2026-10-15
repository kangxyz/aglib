/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Free
public import Aglib.CategoryTheory.Adjunction.MateHomEquiv
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
Source: `Quillen/AlgebraicGeometry/Scheme/Sheaf/PullbackUnit.lean` at LOCAL Quillen
`189a8e779f0c68b2dfc6f8195daebb3e684a5905`. Selection: whole_general_prerequisite;
source ranges [[1, 185]]. Actual objects, maps and hypotheses are preserved.
-/

/-! # Coherent pullback of structure modules

Composition, identity, equality, and section comparisons retain the original unit maps
and the ordered twofold product of the structure module.
-/

@[expose] public section

noncomputable section
universe u v u' v'
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] Abelian.hasFiniteBiproducts

open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
/-- The original structure-module unit respects composition of scheme maps. -/
theorem unitToPushforwardObjUnit_comp :
    SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom ≫
      (AlgebraicGeometry.Scheme.Modules.pushforward g).map
        (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardComp f g).hom.app
        (SheafOfModules.unit X.ringCatSheaf) =
      SheafOfModules.unitToPushforwardObjUnit (f ≫ g).toRingCatSheafHom := by
  apply AlgebraicGeometry.Scheme.Modules.hom_ext
  intro U
  ext x
  rfl
/-- The canonical pullback-unit comparison is adjoint to the original structure map. -/
theorem pullbackUnitIso_homEquiv {A B : Scheme.{u}} (k : A ⟶ B) :
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction k).homEquiv _ _
      (pullbackUnitIso k).hom =
      SheafOfModules.unitToPushforwardObjUnit k.toRingCatSheafHom := by
  have : (TopologicalSpace.Opens.map k.base).Final := inferInstance
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    k.toRingCatSheafHom
/-- The original pullback-unit isomorphisms respect the actual composition comparison. -/
theorem pullbackUnitIso_comp :
    (AlgebraicGeometry.Scheme.Modules.pullbackComp f g).hom.app
        (SheafOfModules.unit Z.ringCatSheaf) ≫ (pullbackUnitIso (f ≫ g)).hom =
      (AlgebraicGeometry.Scheme.Modules.pullback f).map (pullbackUnitIso g).hom ≫
        (pullbackUnitIso f).hom := by
  have : (TopologicalSpace.Opens.map f.base).Final := inferInstance
  have : (TopologicalSpace.Opens.map g.base).Final := inferInstance
  have : (TopologicalSpace.Opens.map (f ≫ g).base).Final := inferInstance
  have h : (AlgebraicGeometry.Scheme.Modules.pullbackComp f g).inv.app
        (SheafOfModules.unit Z.ringCatSheaf) ≫
      ((AlgebraicGeometry.Scheme.Modules.pullback f).map (pullbackUnitIso g).hom ≫
        (pullbackUnitIso f).hom) = (pullbackUnitIso (f ≫ g)).hom := by
    apply ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
      (f ≫ g)).homEquiv _ _).injective
    rw [homEquiv_conjugate, AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackComp_inv,
      Adjunction.comp_homEquiv]
    change (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
      ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        ((AlgebraicGeometry.Scheme.Modules.pullback f).map (pullbackUnitIso g).hom ≫
          (pullbackUnitIso f).hom)) ≫ _ = _
    rw [Adjunction.homEquiv_naturality_left]
    rw [pullbackUnitIso_homEquiv, pullbackUnitIso_homEquiv,
      Adjunction.homEquiv_naturality_right, pullbackUnitIso_homEquiv]
    exact unitToPushforwardObjUnit_comp f g
  rw [← h, Iso.hom_inv_id_app_assoc]
/-- The original identity pullback comparison agrees with the canonical unit comparison. -/
theorem pullbackUnitIso_id (A : Scheme.{u}) :
    (AlgebraicGeometry.Scheme.Modules.pullbackId A).hom.app
      (SheafOfModules.unit A.ringCatSheaf) = (pullbackUnitIso (𝟙 A)).hom := by
  apply ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
    (𝟙 A)).homEquiv _ _).injective
  calc
    _ = (conjugateEquiv Adjunction.id
        (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (𝟙 A))
        (AlgebraicGeometry.Scheme.Modules.pullbackId A).hom).app
          (SheafOfModules.unit A.ringCatSheaf) := homEquiv_to_identity _ _ _
    _ = (AlgebraicGeometry.Scheme.Modules.pushforwardId A).inv.app
        (SheafOfModules.unit A.ringCatSheaf) :=
      congrArg (fun η => η.app (SheafOfModules.unit A.ringCatSheaf))
        (AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackId_hom A)
    _ = SheafOfModules.unitToPushforwardObjUnit
        (AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom (𝟙 A)) := by
      apply AlgebraicGeometry.Scheme.Modules.hom_ext
      intro U
      ext x
      rfl
    _ = _ := (pullbackUnitIso_homEquiv (𝟙 A)).symm
/-- Equal scheme morphisms retain the original unit comparison. -/
theorem pullbackUnitIso_congr {A B : Scheme.{u}} {k l : A ⟶ B} (h : k = l) :
    (AlgebraicGeometry.Scheme.Modules.pullbackCongr h).hom.app
      (SheafOfModules.unit B.ringCatSheaf) ≫ (pullbackUnitIso l).hom =
      (pullbackUnitIso k).hom := by
  subst l
  simp [AlgebraicGeometry.Scheme.Modules.pullbackCongr]
end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules
/-- The actual pullback comparison for the square of structure modules. -/
def pullbackUnitSquareIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (AlgebraicGeometry.Scheme.Modules.pullback f).obj
        ((SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⨯
          SheafOfModules.unit Y.ringCatSheaf) ≅
      ((SheafOfModules.unit X.ringCatSheaf : X.Modules) ⨯
        SheafOfModules.unit X.ringCatSheaf) :=
  PreservesLimitPair.iso (AlgebraicGeometry.Scheme.Modules.pullback f) _ _ ≪≫
    prod.mapIso (pullbackUnitIso f) (pullbackUnitIso f)
@[reassoc (attr := simp)]
theorem pullbackUnitSquareIso_hom_fst {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackUnitSquareIso f).hom ≫ prod.fst =
      (AlgebraicGeometry.Scheme.Modules.pullback f).map prod.fst ≫ (pullbackUnitIso f).hom := by
  simp [pullbackUnitSquareIso]
@[reassoc (attr := simp)]
theorem pullbackUnitSquareIso_hom_snd {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (pullbackUnitSquareIso f).hom ≫ prod.snd =
      (AlgebraicGeometry.Scheme.Modules.pullback f).map prod.snd ≫ (pullbackUnitIso f).hom := by
  simp [pullbackUnitSquareIso]
/-- The canonical pullback square comparison respects composition. -/
theorem pullbackUnitSquareIso_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (AlgebraicGeometry.Scheme.Modules.pullbackComp f g).hom.app
        ((SheafOfModules.unit Z.ringCatSheaf : Z.Modules) ⨯
          SheafOfModules.unit Z.ringCatSheaf) ≫ (pullbackUnitSquareIso (f ≫ g)).hom =
      (AlgebraicGeometry.Scheme.Modules.pullback f).map (pullbackUnitSquareIso g).hom ≫
        (pullbackUnitSquareIso f).hom := by
  apply prod.hom_ext
  · simp only [Category.assoc, pullbackUnitSquareIso_hom_fst]
    rw [← Category.assoc,
      ← (AlgebraicGeometry.Scheme.Modules.pullbackComp f g).hom.naturality prod.fst]
    dsimp only [Functor.comp_map]
    rw [Category.assoc, pullbackUnitIso_comp]
    rw [← Category.assoc, ← Functor.map_comp, ← pullbackUnitSquareIso_hom_fst, Functor.map_comp]
    simp only [Category.assoc]
  · simp only [Category.assoc, pullbackUnitSquareIso_hom_snd]
    rw [← Category.assoc,
      ← (AlgebraicGeometry.Scheme.Modules.pullbackComp f g).hom.naturality prod.snd]
    dsimp only [Functor.comp_map]
    rw [Category.assoc, pullbackUnitIso_comp]
    rw [← Category.assoc, ← Functor.map_comp, ← pullbackUnitSquareIso_hom_snd, Functor.map_comp]
    simp only [Category.assoc]
/-- The identity square comparison is the original identity pullback. -/
theorem pullbackUnitSquareIso_id (X : Scheme.{u}) :
    (AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app
      ((SheafOfModules.unit X.ringCatSheaf : X.Modules) ⨯
        SheafOfModules.unit X.ringCatSheaf) = (pullbackUnitSquareIso (𝟙 X)).hom := by
  apply prod.hom_ext
  · rw [pullbackUnitSquareIso_hom_fst, ← pullbackUnitIso_id]
    exact ((AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.naturality prod.fst).symm
  · rw [pullbackUnitSquareIso_hom_snd, ← pullbackUnitIso_id]
    exact ((AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.naturality prod.snd).symm
/-- Equal morphisms retain the actual square comparison. -/
theorem pullbackUnitSquareIso_congr {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) :
    (AlgebraicGeometry.Scheme.Modules.pullbackCongr h).hom.app
        ((SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⨯
          SheafOfModules.unit Y.ringCatSheaf) ≫ (pullbackUnitSquareIso g).hom =
      (pullbackUnitSquareIso f).hom := by
  subst g
  simp [AlgebraicGeometry.Scheme.Modules.pullbackCongr]
/-- The actual pullback identification along a section of a scheme morphism. -/
def sectionPullbackIso {X Y : Scheme.{u}} (s : Y ⟶ X) (p : X ⟶ Y) (h : s ≫ p = 𝟙 Y) :
    AlgebraicGeometry.Scheme.Modules.pullback p ⋙ AlgebraicGeometry.Scheme.Modules.pullback s ≅
      𝟭 Y.Modules :=
  AlgebraicGeometry.Scheme.Modules.pullbackComp s p ≪≫
    AlgebraicGeometry.Scheme.Modules.pullbackCongr h ≪≫
      AlgebraicGeometry.Scheme.Modules.pullbackId Y
/-- The section identification preserves the literal square of structure modules. -/
theorem sectionPullbackIso_unitSquare {X Y : Scheme.{u}}
    (s : Y ⟶ X) (p : X ⟶ Y) (h : s ≫ p = 𝟙 Y) :
    (sectionPullbackIso s p h).hom.app
        ((SheafOfModules.unit Y.ringCatSheaf : Y.Modules) ⨯
          SheafOfModules.unit Y.ringCatSheaf) =
      (AlgebraicGeometry.Scheme.Modules.pullback s).map (pullbackUnitSquareIso p).hom ≫
        (pullbackUnitSquareIso s).hom := by
  simp only [sectionPullbackIso, Iso.trans_hom, NatTrans.comp_app]
  rw [pullbackUnitSquareIso_id, pullbackUnitSquareIso_congr, pullbackUnitSquareIso_comp]
end AlgebraicGeometry.Scheme.Modules
