/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Tensor.Basic
public import Aglib.Algebra.Category.ModuleCat.Sheaf.TensorPushforwardMap

/-!
# The canonical tensor comparison for module pullback

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
variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The canonical ringed-site tensor map for the scheme direct image. -/
def pushforwardTensorMap (M N : X.Modules) :
    (show Y.Modules from tensorSheaf Y ((Scheme.Modules.pushforward f).obj M)
      ((Scheme.Modules.pushforward f).obj N)) ⟶
      (Scheme.Modules.pushforward f).obj (tensorSheaf X M N) :=
  SheafOfModulesOfCommRing.pushforwardTensorMap
    (F := Opens.map f.base) (S := Y.sheaf) (R := X.sheaf) ⟨f.c⟩ M N

/-- Direct-image tensoring preserves the original sheafification generators. -/
theorem pushforwardTensorMap_tmul (M N : X.Modules) (U : Y.Opensᵒᵖ)
    (m : M.val.obj (op (f ⁻¹ᵁ U.unop))) (n : N.val.obj (op (f ⁻¹ᵁ U.unop))) :
    (pushforwardTensorMap f M N).val.app U
      ((tensorSheafUnit Y ((Scheme.Modules.pushforward f).obj M)
        ((Scheme.Modules.pushforward f).obj N)).app U (m ⊗ₜ n)) =
      (tensorSheafUnit X M N).app (op (f ⁻¹ᵁ U.unop)) (m ⊗ₜ n) := by
  exact SheafOfModulesOfCommRing.pushforwardTensorMap_tensorSection
    (F := Opens.map f.base) (S := Y.sheaf) (R := X.sheaf) ⟨f.c⟩ M N U m n

/-- Naturality of the same direct-image tensor map in both factors. -/
@[reassoc] theorem pushforwardTensorMap_naturality
    {M M' N N' : X.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    tensorSheafMap Y ((Scheme.Modules.pushforward f).map a) ((Scheme.Modules.pushforward f).map b) ≫
        pushforwardTensorMap f M' N' =
      pushforwardTensorMap f M N ≫ (Scheme.Modules.pushforward f).map (tensorSheafMap X a b) := by
  simpa only [pushforwardTensorMap, tensorSheafMap, Scheme.Modules.pushforward,
    SheafOfModulesOfCommRing.modulePushforward, Scheme.Hom.toRingCatSheafHom] using
    (SheafOfModulesOfCommRing.pushforwardTensorMap_naturality
      (F := Opens.map f.base) (S := Y.sheaf) (R := X.sheaf) ⟨f.c⟩ a b)

/-- The canonical pullback tensor comparison defined by the actual adjunction. -/
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
end AlgebraicGeometry.Scheme.Modules
