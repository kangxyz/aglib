/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.Pullback

/-!
# The canonical tensor comparison for module pullback

The pushforward comparison is induced by the actual sectionwise bilinear
map into the sheafified tensor product. Its pure-tensor formula and
naturality are proved. Tensoring the pullback adjunction units and applying
this comparison gives the canonical map from the pullback of a tensor product
to the tensor product of the pullbacks. Its unit compatibility proves
invertibility when the first factor is globally trivial.
The local rank-one case is supplied by `PullbackTensor.Local`; this module
assumes no tensor-pullback theorem-family premise.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Picard.PullbackTensor`
at revision `95a3772b895fbc19a81684be4ffd519d0fdcd6b3`.
The primary namespace is `AlgebraicGeometry.Scheme.Modules.Invertible`;
source names are provenance.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option linter.style.haveILetI false
open CategoryTheory Limits AlgebraicGeometry Opposite
namespace AlgebraicGeometry.Scheme.Modules.Invertible
universe u
variable (X : Scheme.{u})
/-- The sheafification unit from the sectionwise tensor presheaf to the actual tensor sheaf. -/
def tensorSheafUnit (M N : SheafOfModules.{u} X.ringCatSheaf) :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val ⟶
      (tensorSheaf X M N).val :=
  (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app _

variable {M M' M'' N N' N'' : SheafOfModules.{u} X.ringCatSheaf}
@[reassoc] theorem tensorSheafMap_comp (a : M ⟶ M') (b : N ⟶ N')
    (c : M' ⟶ M'') (d : N' ⟶ N'') :
    tensorSheafMap X a b ≫ tensorSheafMap X c d = tensorSheafMap X (a ≫ c) (b ≫ d) := by
  unfold tensorSheafMap
  rw [← Functor.map_comp]
  congr 1
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  rfl

@[reassoc] theorem tensorSheafUnit_naturality (a : M ⟶ M') (b : N ⟶ N') :
    tensorSheafUnit X M N ≫ (tensorSheafMap X a b).val =
      PresheafOfModulesOfCommRing.Monoidal.tensorHom a.val b.val ≫ tensorSheafUnit X M' N' :=
  ((_root_.PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.naturality _).symm

theorem tensorSheafMap_tmul (a : M ⟶ M') (b : N ⟶ N')
    (U : X.Opensᵒᵖ) (m : M.val.obj U) (n : N.val.obj U) :
    (tensorSheafMap X a b).val.app U ((tensorSheafUnit X M N).app U (m ⊗ₜ n)) =
      (tensorSheafUnit X M' N').app U (a.val.app U m ⊗ₜ b.val.app U n) :=
  congrArg (fun k ↦ k.app U (m ⊗ₜ n)) (tensorSheafUnit_naturality X a b)

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
/-- The sectionwise comparison from the tensor of direct images to the direct image of the
tensor. -/
def pushforwardTensorPresheaf (M N : X.Modules) :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := Y.presheaf)
      ((Scheme.Modules.pushforward f).obj M).val ((Scheme.Modules.pushforward f).obj N).val ⟶
        ((Scheme.Modules.pushforward f).obj (tensorSheaf X M N)).val :=
  PresheafOfModulesOfCommRing.homMk (fun U ↦
    ModuleCat.MonoidalCategory.tensorLift
      (fun m n ↦ (tensorSheafUnit X M N).app (op (f ⁻¹ᵁ U.unop)) (m ⊗ₜ n))
      (by intro m m' n; simp only [TensorProduct.add_tmul, map_add])
      (by
        intro r m n
        change M.val.obj (op (f ⁻¹ᵁ U.unop)) at m
        change N.val.obj (op (f ⁻¹ᵁ U.unop)) at n
        change (tensorSheafUnit X M N).app _ ((f.app U.unop r • m) ⊗ₜ n) =
          f.app U.unop r • (tensorSheafUnit X M N).app _ (m ⊗ₜ n)
        exact ((tensorSheafUnit X M N).app _).hom.map_smul (f.app U.unop r) (m ⊗ₜ n))
      (by intro m n n'; simp only [TensorProduct.tmul_add, map_add])
      (by
        intro r m n
        change M.val.obj (op (f ⁻¹ᵁ U.unop)) at m
        change N.val.obj (op (f ⁻¹ᵁ U.unop)) at n
        change (tensorSheafUnit X M N).app _ (m ⊗ₜ (f.app U.unop r • n)) =
          f.app U.unop r • (tensorSheafUnit X M N).app _ (m ⊗ₜ n)
        rw [TensorProduct.tmul_smul, _root_.map_smul]))
    (by
      intro U V i
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro m n
      exact congrArg (fun k ↦ k.hom (m ⊗ₜ n))
        ((tensorSheafUnit X M N).naturality ((TopologicalSpace.Opens.map f.base).map i.unop).op))

/-- The sheafified comparison from the tensor of direct images to the direct image of the
tensor. -/
def pushforwardTensorMap (M N : X.Modules) :
    (show Y.Modules from tensorSheaf Y ((Scheme.Modules.pushforward f).obj M)
      ((Scheme.Modules.pushforward f).obj N)) ⟶
      (Scheme.Modules.pushforward f).obj (tensorSheaf X M N) :=
  (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 Y.ringCatSheaf.obj)).symm
    (pushforwardTensorPresheaf f M N)

theorem pushforwardTensorMap_tmul (M N : X.Modules) (U : Y.Opensᵒᵖ)
    (m : M.val.obj (op (f ⁻¹ᵁ U.unop))) (n : N.val.obj (op (f ⁻¹ᵁ U.unop))) :
    (pushforwardTensorMap f M N).val.app U
      ((tensorSheafUnit Y ((Scheme.Modules.pushforward f).obj M)
        ((Scheme.Modules.pushforward f).obj N)).app U (m ⊗ₜ n)) =
      (tensorSheafUnit X M N).app (op (f ⁻¹ᵁ U.unop)) (m ⊗ₜ n) := by
  have h := (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 Y.ringCatSheaf.obj)
    (F := (Scheme.Modules.pushforward f).obj (tensorSheaf X M N))).apply_symm_apply
    (pushforwardTensorPresheaf f M N)
  exact congrArg (fun k ↦ k.app U (m ⊗ₜ n)) h

@[reassoc] theorem pushforwardTensorMap_naturality
    {M M' N N' : X.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    tensorSheafMap Y ((Scheme.Modules.pushforward f).map a) ((Scheme.Modules.pushforward f).map b) ≫
        pushforwardTensorMap f M' N' =
      pushforwardTensorMap f M N ≫ (Scheme.Modules.pushforward f).map (tensorSheafMap X a b) := by
  apply (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 Y.ringCatSheaf.obj)).injective
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  change (pushforwardTensorMap f M' N').val.app U
    ((tensorSheafMap Y ((Scheme.Modules.pushforward f).map a)
      ((Scheme.Modules.pushforward f).map b)).val.app U
      ((tensorSheafUnit Y ((Scheme.Modules.pushforward f).obj M)
        ((Scheme.Modules.pushforward f).obj N)).app U (m ⊗ₜ n))) =
    (tensorSheafMap X a b).val.app (op (f ⁻¹ᵁ U.unop))
      ((pushforwardTensorMap f M N).val.app U
        ((tensorSheafUnit Y ((Scheme.Modules.pushforward f).obj M)
          ((Scheme.Modules.pushforward f).obj N)).app U (m ⊗ₜ n)))
  rw [tensorSheafMap_tmul, pushforwardTensorMap_tmul,
    pushforwardTensorMap_tmul, tensorSheafMap_tmul]
  rfl

/-- The map from pullback of the tensor to tensor of the pullbacks, defined by the actual
geometric adjunction. -/
def pullbackTensorMap (M N : Y.Modules) :
    (Scheme.Modules.pullback f).obj (tensorSheaf Y M N) ⟶
      (show X.Modules from tensorSheaf X ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N)) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
    (tensorSheafMap Y ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
      pushforwardTensorMap f ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N))
@[simp] theorem pullbackTensorMap_adjoint (M N : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackTensorMap f M N) =
      tensorSheafMap Y ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
        pushforwardTensorMap f ((Scheme.Modules.pullback f).obj M)
          ((Scheme.Modules.pullback f).obj N) :=
  Equiv.apply_symm_apply _ _

@[reassoc] theorem pullbackTensorMap_naturality
    {M M' N N' : Y.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    (Scheme.Modules.pullback f).map (tensorSheafMap Y a b) ≫ pullbackTensorMap f M' N' =
      pullbackTensorMap f M N ≫
        tensorSheafMap X ((Scheme.Modules.pullback f).map a)
          ((Scheme.Modules.pullback f).map b) := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right,
    pullbackTensorMap_adjoint, pullbackTensorMap_adjoint]
  rw [Category.assoc, ← pushforwardTensorMap_naturality, ← Category.assoc,
    tensorSheafMap_comp, ← Category.assoc, tensorSheafMap_comp]
  congr 1
  exact congrArg₂ (fun c d ↦ tensorSheafMap Y c d)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality a)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality b)
end AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Modules.Invertible
universe u
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

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
theorem pullbackUnitIso_adjoint :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (SheafOfModules.unit Y.ringCatSheaf) ≫
      (Scheme.Modules.pushforward f).map (pullbackUnitIso f).hom =
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _

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
  have hu := pullbackUnitIso_adjoint f
  rw [hu]
  exact (pushforwardTensorMap_leftUnit f M).trans
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality _)
end AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Modules.Invertible
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
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
end AlgebraicGeometry.Scheme.Modules.Invertible

namespace AlgebraicGeometry.Scheme.Modules.Invertible
universe u
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
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
end AlgebraicGeometry.Scheme.Modules.Invertible
