/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Basic
public import Aglib.AlgebraicGeometry.Modules.Pullback.Unit

/-!
# Unit compatibility of the canonical pullback tensor map

These are the existing canonical module-sheaf constructions and their actual map
identities. Scheme, morphism and coefficient hypotheses remain unchanged.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules
universe u
section TensorUnit
variable (X : Scheme.{u})

theorem tensorSheafLeftUnit_tmul (M : X.Modules) (U : X.Opensᵒᵖ)
    (r : X.presheaf.obj U) (m : M.val.obj U) :
    (tensorSheafLeftUnit X M).hom.val.app U
      ((tensorSheafUnit X (SheafOfModules.unit X.ringCatSheaf) M).app U (r ⊗ₜ m)) = r • m := by
  let adj := _root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  letI : MonoidalCategory (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
    inferInstanceAs (MonoidalCategory (PresheafOfModulesOfCommRing.{u} X.presheaf))
  let l := (MonoidalCategory.leftUnitor M.val).hom
  have h : tensorSheafUnit X (SheafOfModules.unit X.ringCatSheaf) M ≫
      (tensorSheafLeftUnit X M).hom.val = l := by
    change (adj.homEquiv _ _ (tensorSheafLeftUnit X M).hom) = l
    have hl : (tensorSheafLeftUnit X M).hom = (adj.homEquiv _ _).symm l :=
      (adj.homEquiv_counit _ _ l).symm
    rw [hl]
    exact (adj.homEquiv _ _).apply_symm_apply l
  exact congrArg (fun k ↦ k.app U (r ⊗ₜ m)) h

end TensorUnit

section PullbackUnit
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

theorem pushforwardTensorMap_leftUnit (M : Y.Modules) :
    tensorSheafMap Y (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
      pushforwardTensorMap f (SheafOfModules.unit X.ringCatSheaf)
        ((Scheme.Modules.pullback f).obj M) ≫
      (Scheme.Modules.pushforward f).map
        (tensorSheafLeftUnit X ((Scheme.Modules.pullback f).obj M)).hom =
    (tensorSheafLeftUnit Y M).hom ≫
      (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M := by
  apply (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 Y.ringCatSheaf.obj)).injective
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro r m
  change Y.presheaf.obj U at r
  change M.val.obj U at m
  change (tensorSheafLeftUnit X ((Scheme.Modules.pullback f).obj M)).hom.val.app (op (f ⁻¹ᵁ U.unop))
    ((pushforwardTensorMap f (SheafOfModules.unit X.ringCatSheaf)
      ((Scheme.Modules.pullback f).obj M)).val.app U
      ((tensorSheafMap Y (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)).val.app U
          ((tensorSheafUnit Y (SheafOfModules.unit Y.ringCatSheaf) M).app U (r ⊗ₜ m)))) =
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app U
      ((tensorSheafLeftUnit Y M).hom.val.app U
        ((tensorSheafUnit Y (SheafOfModules.unit Y.ringCatSheaf) M).app U (r ⊗ₜ m)))
  have h₁ := tensorSheafMap_tmul Y
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) U r m
  have h₂ := pushforwardTensorMap_tmul f (SheafOfModules.unit X.ringCatSheaf)
    ((Scheme.Modules.pullback f).obj M) U
    (f.app U.unop r) (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app U m)
  have h₃ := tensorSheafLeftUnit_tmul X ((Scheme.Modules.pullback f).obj M)
    (op (f ⁻¹ᵁ U.unop)) (f.app U.unop r)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app U m)
  have h₄ := tensorSheafLeftUnit_tmul Y M U r m
  exact (congrArg (fun z ↦
      (tensorSheafLeftUnit X ((Scheme.Modules.pullback f).obj M)).hom.val.app
        (op (f ⁻¹ᵁ U.unop)) z)
    ((congrArg (fun z ↦ (pushforwardTensorMap f (SheafOfModules.unit X.ringCatSheaf)
      ((Scheme.Modules.pullback f).obj M)).val.app U z) h₁).trans h₂)).trans
    (h₃.trans
      (((((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app U).hom.map_smul
        r m).symm.trans
      (congrArg
        (fun z ↦ ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app U z)
        h₄.symm)))

theorem pullbackTensorMap_leftUnit (M : Y.Modules) :
    pullbackTensorMap f (SheafOfModules.unit Y.ringCatSheaf) M ≫
        tensorSheafMap X (pullbackUnitIso f).hom (𝟙 ((Scheme.Modules.pullback f).obj M)) ≫
        (tensorSheafLeftUnit X ((Scheme.Modules.pullback f).obj M)).hom =
      (Scheme.Modules.pullback f).map (tensorSheafLeftUnit Y M).hom := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_right, pullbackTensorMap_adjoint, Functor.map_comp]
  simp only [Category.assoc]
  have hn := pushforwardTensorMap_naturality_assoc f (pullbackUnitIso f).hom
    (𝟙 ((Scheme.Modules.pullback f).obj M))
    ((Scheme.Modules.pushforward f).map
      (tensorSheafLeftUnit X ((Scheme.Modules.pullback f).obj M)).hom)
  rw [← hn]
  rw [tensorSheafMap_comp_assoc]
  have hu := pullbackUnitIso_homEquiv f
  change (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
      (SheafOfModules.unit Y.ringCatSheaf) ≫
    (Scheme.Modules.pushforward f).map (pullbackUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom at hu
  rw [hu]
  exact (pushforwardTensorMap_leftUnit f M).trans
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality _)

theorem pullbackTensorMap_leftUnit_isIso (M : Y.Modules) :
    IsIso (pullbackTensorMap f (SheafOfModules.unit Y.ringCatSheaf) M) := by
  let e := tensorSheafIso X (pullbackUnitIso f) (Iso.refl ((Scheme.Modules.pullback f).obj M))
  haveI : IsIso
      (tensorSheafMap X (pullbackUnitIso f).hom (𝟙 ((Scheme.Modules.pullback f).obj M))) :=
    e.isIso_hom
  haveI : IsIso (pullbackTensorMap f (SheafOfModules.unit Y.ringCatSheaf) M ≫
      tensorSheafMap X (pullbackUnitIso f).hom (𝟙 ((Scheme.Modules.pullback f).obj M)) ≫
      (tensorSheafLeftUnit X ((Scheme.Modules.pullback f).obj M)).hom) := by
    rw [pullbackTensorMap_leftUnit]
    infer_instance
  exact IsIso.of_isIso_comp_right
    (pullbackTensorMap f (SheafOfModules.unit Y.ringCatSheaf) M)
    (tensorSheafMap X (pullbackUnitIso f).hom (𝟙 ((Scheme.Modules.pullback f).obj M)) ≫
      (tensorSheafLeftUnit X ((Scheme.Modules.pullback f).obj M)).hom)

theorem pullbackTensorMap_isIso_of_trivial_left (M N : Y.Modules)
    (e : M ≅ (show Y.Modules from SheafOfModules.unit Y.ringCatSheaf)) :
    IsIso (pullbackTensorMap f M N) := by
  haveI := pullbackTensorMap_leftUnit_isIso f N
  haveI : IsIso (tensorSheafMap Y e.hom (𝟙 N)) :=
    (tensorSheafIso Y e (Iso.refl N)).isIso_hom
  haveI : IsIso (tensorSheafMap X ((Scheme.Modules.pullback f).map e.hom)
      ((Scheme.Modules.pullback f).map (𝟙 N))) := by
    have h : IsIso (tensorSheafMap X ((Scheme.Modules.pullback f).map e.hom)
        (𝟙 ((Scheme.Modules.pullback f).obj N))) :=
      (tensorSheafIso X ((Scheme.Modules.pullback f).mapIso e)
        (Iso.refl ((Scheme.Modules.pullback f).obj N))).isIso_hom
    convert h using 1
    exact congrArg (tensorSheafMap X ((Scheme.Modules.pullback f).map e.hom))
      ((Scheme.Modules.pullback f).map_id N)
  haveI : IsIso (pullbackTensorMap f M N ≫
      tensorSheafMap X ((Scheme.Modules.pullback f).map e.hom)
        ((Scheme.Modules.pullback f).map (𝟙 N))) := by
    rw [← pullbackTensorMap_naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right (pullbackTensorMap f M N)
    (tensorSheafMap X ((Scheme.Modules.pullback f).map e.hom)
      ((Scheme.Modules.pullback f).map (𝟙 N)))
end PullbackUnit
end AlgebraicGeometry.Scheme.Modules
