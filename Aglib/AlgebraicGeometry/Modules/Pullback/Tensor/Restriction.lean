/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Basic
public import Aglib.AlgebraicGeometry.Modules.Tensor.Restriction
public import Aglib.AlgebraicGeometry.Modules.Tensor.Sections
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
# Restriction of the canonical pullback tensor comparison

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
open AlgebraicGeometry.Scheme.Modules.Pullback.OpenRestriction
section OpenTensor
variable (X : Scheme.{u}) (U : X.Opens) (M N : X.Modules)

/-- The canonical open-restriction tensor arrow. -/
def restrictTensorMap :
    (show U.toScheme.Modules from tensorSheaf U.toScheme
      ((Scheme.Modules.restrictFunctor U.ι).obj M)
      ((Scheme.Modules.restrictFunctor U.ι).obj N)) ⟶
      (Scheme.Modules.restrictFunctor U.ι).obj (tensorSheaf X M N) :=
  (tensorRestrictionIso U.ι M N).hom

/-- The canonical restriction tensor arrow is invertible for arbitrary modules. -/
theorem restrictTensorMap_isIso : IsIso (restrictTensorMap X U M N) :=
  (tensorRestrictionIso U.ι M N).isIso_hom

/-- The existing open-restriction tensor isomorphism. -/
def restrictTensorIso :
    (show U.toScheme.Modules from tensorSheaf U.toScheme
      ((Scheme.Modules.restrictFunctor U.ι).obj M)
      ((Scheme.Modules.restrictFunctor U.ι).obj N)) ≅
      (Scheme.Modules.restrictFunctor U.ι).obj (tensorSheaf X M N) :=
  tensorRestrictionIso U.ι M N

@[simp] theorem restrictTensorIso_hom :
    (restrictTensorIso X U M N).hom = restrictTensorMap X U M N := rfl

theorem restrictTensorMap_tmul (V : U.toScheme.Opensᵒᵖ)
    (m : M.val.obj (op (U.ι ''ᵁ V.unop)))
    (n : N.val.obj (op (U.ι ''ᵁ V.unop))) :
    (restrictTensorMap X U M N).val.app V
      ((tensorSheafUnit U.toScheme ((Scheme.Modules.restrictFunctor U.ι).obj M)
        ((Scheme.Modules.restrictFunctor U.ι).obj N)).app V (m ⊗ₜ n)) =
      (tensorSheafUnit X M N).app (op (U.ι ''ᵁ V.unop)) (m ⊗ₜ n) := by
  exact SheafOfModulesOfCommRing.pushforwardTensorMap_tensorSection
    (restrictionRingHom U.ι) M N V m n

@[reassoc] theorem restrictTensorMap_naturality
    {M M' N N' : X.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    tensorSheafMap U.toScheme ((Scheme.Modules.restrictFunctor U.ι).map a)
        ((Scheme.Modules.restrictFunctor U.ι).map b) ≫ restrictTensorMap X U M' N' =
      restrictTensorMap X U M N ≫ (Scheme.Modules.restrictFunctor U.ι).map
        (tensorSheafMap X a b) := by
  simpa only [restrictTensorMap, tensorRestrictionIso, tensorSheafMap,
    Scheme.Modules.restrictFunctor, SheafOfModulesOfCommRing.modulePushforward,
    restrictionRingHom] using
    (SheafOfModulesOfCommRing.tensorPushforwardIso_naturality
      (restrictionRingHom U.ι) a b)

end OpenTensor

section PullbackRestriction
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)

@[reassoc] theorem restrictedPushforward_tensor (M N : X.Modules) :
    tensorSheafMap U.toScheme (restrictedPushforwardMap f U M)
        (restrictedPushforwardMap f U N) ≫
      pushforwardTensorMap (f ∣_ U)
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj M)
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj N) ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map
        (restrictTensorMap X (f ⁻¹ᵁ U) M N) =
    restrictTensorMap Y U ((Scheme.Modules.pushforward f).obj M)
        ((Scheme.Modules.pushforward f).obj N) ≫
      (Scheme.Modules.restrictFunctor U.ι).map (pushforwardTensorMap f M N) ≫
      restrictedPushforwardMap f U (show X.Modules from tensorSheaf X M N) := by
  apply (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 U.toScheme.ringCatSheaf.obj)).injective
  ext W : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  change (restrictTensorMap X (f ⁻¹ᵁ U) M N).val.app (op ((f ∣_ U) ⁻¹ᵁ W.unop))
    ((pushforwardTensorMap (f ∣_ U)
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj M)
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj N)).val.app W
      ((tensorSheafMap U.toScheme (restrictedPushforwardMap f U M)
        (restrictedPushforwardMap f U N)).val.app W
        ((tensorSheafUnit U.toScheme
          ((Scheme.Modules.restrictFunctor U.ι).obj ((Scheme.Modules.pushforward f).obj M))
          ((Scheme.Modules.restrictFunctor U.ι).obj ((Scheme.Modules.pushforward f).obj N))).app W
          (m ⊗ₜ n)))) =
    (restrictedPushforwardMap f U (show X.Modules from tensorSheaf X M N)).val.app W
      ((pushforwardTensorMap f M N).val.app (op (U.ι ''ᵁ W.unop))
        ((restrictTensorMap Y U ((Scheme.Modules.pushforward f).obj M)
          ((Scheme.Modules.pushforward f).obj N)).val.app W
          ((tensorSheafUnit U.toScheme
            ((Scheme.Modules.restrictFunctor U.ι).obj ((Scheme.Modules.pushforward f).obj M))
            ((Scheme.Modules.restrictFunctor U.ι).obj ((Scheme.Modules.pushforward f).obj N))).app W
            (m ⊗ₜ n))))
  rw [tensorSheafMap_tmul, pushforwardTensorMap_tmul, restrictTensorMap_tmul,
    restrictTensorMap_tmul, pushforwardTensorMap_tmul,
    restrictedPushforwardMap_apply, restrictedPushforwardMap_apply, restrictedPushforwardMap_apply]
  exact congrArg (fun k ↦ k.hom (m ⊗ₜ n))
    ((tensorSheafUnit X M N).naturality
      (eqToHom (image_morphismRestrict_preimage f U W.unop)).op)

@[reassoc] theorem pullbackTensorMap_restrict (M N : Y.Modules) :
    (Scheme.Modules.pullback (f ∣_ U)).map (restrictTensorMap Y U M N) ≫
      (localPullbackIso f U).inv.app (show Y.Modules from tensorSheaf Y M N) ≫
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map (pullbackTensorMap f M N) =
    pullbackTensorMap (f ∣_ U) ((Scheme.Modules.restrictFunctor U.ι).obj M)
        ((Scheme.Modules.restrictFunctor U.ι).obj N) ≫
      tensorSheafMap (f ⁻¹ᵁ U).toScheme ((localPullbackIso f U).inv.app M)
        ((localPullbackIso f U).inv.app N) ≫
      restrictTensorMap X (f ⁻¹ᵁ U) ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N) := by
  have h := restrictedAdjoint_eq f U
    (tensorSheafMap Y ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
      pushforwardTensorMap f ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N))
  change (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map (pullbackTensorMap f M N) = _ at h
  erw [h]
  erw [Iso.inv_hom_id_app_assoc]
  apply ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _).injective
  erw [Adjunction.homEquiv_naturality_left, Equiv.apply_symm_apply,
    Adjunction.homEquiv_naturality_right, pullbackTensorMap_adjoint,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]
  have hn := pushforwardTensorMap_naturality_assoc (f ∣_ U)
    ((localPullbackIso f U).inv.app M) ((localPullbackIso f U).inv.app N)
    ((Scheme.Modules.pushforward (f ∣_ U)).map
      (restrictTensorMap X (f ⁻¹ᵁ U) ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N)))
  erw [← hn]
  have hc := tensorSheafMap_comp_assoc U.toScheme
    ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app
      ((Scheme.Modules.restrictFunctor U.ι).obj M))
    ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app
      ((Scheme.Modules.restrictFunctor U.ι).obj N))
    ((Scheme.Modules.pushforward (f ∣_ U)).map ((localPullbackIso f U).inv.app M))
    ((Scheme.Modules.pushforward (f ∣_ U)).map ((localPullbackIso f U).inv.app N))
    (pushforwardTensorMap (f ∣_ U)
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback f).obj M))
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback f).obj N)) ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map
        (restrictTensorMap X (f ⁻¹ᵁ U) ((Scheme.Modules.pullback f).obj M)
          ((Scheme.Modules.pullback f).obj N)))
  erw [hc, restrictedUnit f U M, restrictedUnit f U N]
  have hr := restrictTensorMap_naturality_assoc Y U
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N)
    ((Scheme.Modules.restrictFunctor U.ι).map
      (pushforwardTensorMap f ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N)) ≫
      restrictedPushforwardMap f U (show X.Modules from tensorSheaf X
        ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N)))
  erw [← hr]
  have hd := tensorSheafMap_comp_assoc U.toScheme
    ((Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M))
    ((Scheme.Modules.restrictFunctor U.ι).map
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N))
    (restrictedPushforwardMap f U ((Scheme.Modules.pullback f).obj M))
    (restrictedPushforwardMap f U ((Scheme.Modules.pullback f).obj N))
    (pushforwardTensorMap (f ∣_ U)
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback f).obj M))
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj ((Scheme.Modules.pullback f).obj N)) ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map
        (restrictTensorMap X (f ⁻¹ᵁ U) ((Scheme.Modules.pullback f).obj M)
          ((Scheme.Modules.pullback f).obj N)))
  erw [← hd, restrictedPushforward_tensor f U ((Scheme.Modules.pullback f).obj M)
    ((Scheme.Modules.pullback f).obj N)]
  rfl
end PullbackRestriction
end AlgebraicGeometry.Scheme.Modules
