/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: R5Lab contributors
-/
module

public import Aglib.AlgebraicGeometry.Modules.Invertible.PullbackTensor
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction

/-!
# Tensor pullback and the Picard homomorphism

The canonical restriction-tensor comparison is an isomorphism for arbitrary
module sheaves: restriction preserves the local bijectivity of the
sheafification unit. The mate-defined local pullback isomorphism identifies
restriction of the canonical pullback-tensor comparison with the local one.
Applying the global unit case on actual rank-one charts proves that the
comparison is invertible when its first factor is locally rank one; its second
factor is arbitrary. This constructs the canonical line-bundle tensor
pullback isomorphism and the additive Picard pullback homomorphism, including
inverse, identity and composition laws, without an extra tensor-pullback premise.

Extraction source: `R5Lab.AlgebraicGeometry.Curves.Picard.PullbackTensor.Local`
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
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local
universe u
variable (X : Scheme.{u}) (U : X.Opens) (M N : X.Modules)
/-- Restriction of module presheaves to the open subscheme, using its actual scalar comparison. -/
def restrictPresheaf : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj ⥤
    _root_.PresheafOfModules.{u} U.toScheme.ringCatSheaf.obj :=
  let α : U.toScheme.presheaf ⟶ U.ι.opensFunctor.op ⋙ X.presheaf :=
    { app V := (U.ι.appIso V.unop).inv }
  _root_.PresheafOfModules.pushforward (F := U.ι.opensFunctor)
    (Functor.whiskerRight α (forget₂ CommRingCat RingCat))

/-- The section-module identification between open-subscheme restriction and the image open. -/
def restrictSectionIso (P : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj)
    (V : U.toScheme.Opensᵒᵖ) :
    ((restrictPresheaf X U).obj P).obj V ≅ P.obj (op (U.ι ''ᵁ V.unop)) :=
  ModuleCat.isoMk (Iso.refl _) (by
    intro r
    ext m
    change P.obj (op (U.ι ''ᵁ V.unop)) at m
    change X.presheaf.obj (op (U.ι ''ᵁ V.unop)) at r
    change r • m = (U.ι.appIso V.unop).inv r • m
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
    rfl)

/-- The presheaf tensor comparison for the two module sheaves restricted to the open subscheme. -/
def restrictTensorPresheafIso :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := U.toScheme.presheaf)
      ((Scheme.Modules.restrictFunctor U.ι).obj M).val
      ((Scheme.Modules.restrictFunctor U.ι).obj N).val ≅
    (restrictPresheaf X U).obj
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val) :=
  _root_.PresheafOfModules.isoMk (fun V ↦
    (MonoidalCategory.tensorIso (restrictSectionIso X U M.val V)
      (restrictSectionIso X U N.val V)) ≪≫
    (restrictSectionIso X U
      (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val) V).symm)
    (by
      intro V W i
      apply ModuleCat.MonoidalCategory.tensor_ext
      intro m n
      rfl)

/-- The tensor of restricted presheaves mapped to the restriction of the tensor sheaf via its
unit. -/
def restrictTensorUnit :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := U.toScheme.presheaf)
      ((Scheme.Modules.restrictFunctor U.ι).obj M).val
      ((Scheme.Modules.restrictFunctor U.ι).obj N).val ⟶
      ((Scheme.Modules.restrictFunctor U.ι).obj (tensorSheaf X M N)).val :=
  (restrictTensorPresheafIso X U M N).hom ≫
    (restrictPresheaf X U).map (tensorSheafUnit X M N)

/-- The sheafified map from the tensor of restricted module sheaves to the restriction of their
tensor. -/
def restrictTensorMap :
    (show U.toScheme.Modules from tensorSheaf U.toScheme
      ((Scheme.Modules.restrictFunctor U.ι).obj M)
      ((Scheme.Modules.restrictFunctor U.ι).obj N)) ⟶
      (Scheme.Modules.restrictFunctor U.ι).obj (tensorSheaf X M N) :=
  (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 U.toScheme.ringCatSheaf.obj)).symm
    (restrictTensorUnit X U M N)

theorem restrictTensorUnit_factor : restrictTensorUnit X U M N =
    (restrictTensorPresheafIso X U M N).hom ≫
      (restrictPresheaf X U).map (tensorSheafUnit X M N) := by
  ext V : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  rfl

theorem restrictTensorUnit_locallyInjective :
    _root_.PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology U.toScheme)
      (restrictTensorUnit X U M N) := by
  have h : _root_.PresheafOfModules.IsLocallyInjective (Opens.grothendieckTopology U.toScheme)
      ((restrictPresheaf X U).map (tensorSheafUnit X M N)) := by
    change Presheaf.IsLocallyInjective (Opens.grothendieckTopology U.toScheme)
      (Functor.whiskerLeft U.ι.opensFunctor.op
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val).presheaf))
    exact Presheaf.isLocallyInjective_whisker (Opens.grothendieckTopology U.toScheme)
      (Opens.grothendieckTopology X) U.ι.opensFunctor _
  let e := (_root_.PresheafOfModules.toPresheaf U.toScheme.ringCatSheaf.obj).mapIso
    (restrictTensorPresheafIso X U M N)
  haveI : Presheaf.IsLocallyInjective (Opens.grothendieckTopology U.toScheme) e.hom := by
    infer_instance
  haveI : Presheaf.IsLocallyInjective (Opens.grothendieckTopology U.toScheme)
      ((_root_.PresheafOfModules.toPresheaf U.toScheme.ringCatSheaf.obj).map
        ((restrictPresheaf X U).map (tensorSheafUnit X M N))) := h
  exact Presheaf.isLocallyInjective_comp (Opens.grothendieckTopology U.toScheme) e.hom
    ((_root_.PresheafOfModules.toPresheaf U.toScheme.ringCatSheaf.obj).map
      ((restrictPresheaf X U).map (tensorSheafUnit X M N)))

theorem restrictTensorUnit_locallySurjective :
    _root_.PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology U.toScheme)
      (restrictTensorUnit X U M N) := by
  have h : _root_.PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology U.toScheme)
      ((restrictPresheaf X U).map (tensorSheafUnit X M N)) := by
    change Presheaf.IsLocallySurjective (Opens.grothendieckTopology U.toScheme)
      (Functor.whiskerLeft U.ι.opensFunctor.op
        (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
          (PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val).presheaf))
    exact Presheaf.isLocallySurjective_whisker (Opens.grothendieckTopology U.toScheme)
      (Opens.grothendieckTopology X) U.ι.opensFunctor _
  let e := (_root_.PresheafOfModules.toPresheaf U.toScheme.ringCatSheaf.obj).mapIso
    (restrictTensorPresheafIso X U M N)
  haveI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology U.toScheme) e.hom := by
    infer_instance
  haveI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology U.toScheme)
      ((_root_.PresheafOfModules.toPresheaf U.toScheme.ringCatSheaf.obj).map
        ((restrictPresheaf X U).map (tensorSheafUnit X M N))) := h
  exact Presheaf.isLocallySurjective_comp (Opens.grothendieckTopology U.toScheme) e.hom
    ((_root_.PresheafOfModules.toPresheaf U.toScheme.ringCatSheaf.obj).map
      ((restrictPresheaf X U).map (tensorSheafUnit X M N)))

theorem restrictTensorMap_isIso : IsIso (restrictTensorMap X U M N) := by
  let S := _root_.PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)
  have h : IsIso (S.map (restrictTensorUnit X U M N)) := by
    apply Functor.IsLocalization.inverts
      (W := (Opens.grothendieckTopology U.toScheme).W.inverseImage
        (_root_.PresheafOfModules.toPresheaf U.toScheme.ringCatSheaf.obj))
    change (Opens.grothendieckTopology U.toScheme).W
      ((_root_.PresheafOfModules.toPresheaf U.toScheme.ringCatSheaf.obj).map
        (restrictTensorUnit X U M N))
    rw [GrothendieckTopology.W_iff_isLocallyBijective]
    exact ⟨restrictTensorUnit_locallyInjective X U M N,
      restrictTensorUnit_locallySurjective X U M N⟩
  let P := PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := U.toScheme.presheaf)
    ((Scheme.Modules.restrictFunctor U.ι).obj M).val
    ((Scheme.Modules.restrictFunctor U.ι).obj N).val
  let F : SheafOfModules.{u} U.toScheme.ringCatSheaf :=
    (Scheme.Modules.restrictFunctor U.ι).obj (tensorSheaf X M N)
  have he : (_root_.PresheafOfModules.sheafificationAdjunction
      (𝟙 U.toScheme.ringCatSheaf.obj)).homEquiv P F =
      _root_.PresheafOfModules.sheafificationHomEquiv (𝟙 U.toScheme.ringCatSheaf.obj) := by
    ext k
    rfl
  unfold restrictTensorMap
  rw [← he]
  erw [Adjunction.homEquiv_counit]
  let e := asIso (S.map (restrictTensorUnit X U M N)) ≪≫
    asIso ((_root_.PresheafOfModules.sheafificationAdjunction
      (𝟙 U.toScheme.ringCatSheaf.obj)).counit.app F)
  exact e.isIso_hom

/-- Tensor products commute with actual restriction to an open subscheme. -/
def restrictTensorIso :
    (show U.toScheme.Modules from tensorSheaf U.toScheme
      ((Scheme.Modules.restrictFunctor U.ι).obj M)
      ((Scheme.Modules.restrictFunctor U.ι).obj N)) ≅
      (Scheme.Modules.restrictFunctor U.ι).obj (tensorSheaf X M N) := by
  haveI := restrictTensorMap_isIso X U M N
  exact asIso (restrictTensorMap X U M N)

@[simp] theorem restrictTensorIso_hom :
    (restrictTensorIso X U M N).hom = restrictTensorMap X U M N := rfl

theorem restrictTensorMap_tmul (V : U.toScheme.Opensᵒᵖ)
    (m : M.val.obj (op (U.ι ''ᵁ V.unop)))
    (n : N.val.obj (op (U.ι ''ᵁ V.unop))) :
    (restrictTensorMap X U M N).val.app V
      ((tensorSheafUnit U.toScheme ((Scheme.Modules.restrictFunctor U.ι).obj M)
        ((Scheme.Modules.restrictFunctor U.ι).obj N)).app V (m ⊗ₜ n)) =
      (tensorSheafUnit X M N).app (op (U.ι ''ᵁ V.unop)) (m ⊗ₜ n) := by
  have h := (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 U.toScheme.ringCatSheaf.obj)
    (F := (Scheme.Modules.restrictFunctor U.ι).obj (tensorSheaf X M N))).apply_symm_apply
    (restrictTensorUnit X U M N)
  exact congrArg (fun k ↦ k.app V (m ⊗ₜ n)) h

@[reassoc] theorem restrictTensorMap_naturality
    {M M' N N' : X.Modules} (a : M ⟶ M') (b : N ⟶ N') :
    tensorSheafMap U.toScheme ((Scheme.Modules.restrictFunctor U.ι).map a)
        ((Scheme.Modules.restrictFunctor U.ι).map b) ≫ restrictTensorMap X U M' N' =
      restrictTensorMap X U M N ≫ (Scheme.Modules.restrictFunctor U.ι).map
        (tensorSheafMap X a b) := by
  apply (_root_.PresheafOfModules.sheafificationHomEquiv (𝟙 U.toScheme.ringCatSheaf.obj)).injective
  ext V : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  change (restrictTensorMap X U M' N').val.app V
    ((tensorSheafMap U.toScheme ((Scheme.Modules.restrictFunctor U.ι).map a)
      ((Scheme.Modules.restrictFunctor U.ι).map b)).val.app V
      ((tensorSheafUnit U.toScheme ((Scheme.Modules.restrictFunctor U.ι).obj M)
        ((Scheme.Modules.restrictFunctor U.ι).obj N)).app V (m ⊗ₜ n))) =
    (tensorSheafMap X a b).val.app (op (U.ι ''ᵁ V.unop))
      ((restrictTensorMap X U M N).val.app V
        ((tensorSheafUnit U.toScheme ((Scheme.Modules.restrictFunctor U.ι).obj M)
          ((Scheme.Modules.restrictFunctor U.ι).obj N)).app V (m ⊗ₜ n)))
  rw [tensorSheafMap_tmul, restrictTensorMap_tmul, restrictTensorMap_tmul, tensorSheafMap_tmul]
  rfl

end AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local

namespace AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local
universe u
open AlgebraicGeometry.Scheme.Modules.Pullback.OpenRestriction
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
theorem restrictedUnit (M : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).unit.app
        ((Scheme.Modules.restrictFunctor U.ι).obj M) ≫
      (Scheme.Modules.pushforward (f ∣_ U)).map ((localPullbackIso f U).inv.app M) =
    (Scheme.Modules.restrictFunctor U.ι).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
      restrictedPushforwardMap f U ((Scheme.Modules.pullback f).obj M) := by
  let A := Scheme.Modules.pullbackPushforwardAdjunction f
  let B := Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)
  let φ := (Scheme.Modules.restrictFunctor U.ι).map (A.unit.app M) ≫
    restrictedPushforwardMap f U ((Scheme.Modules.pullback f).obj M)
  have h := restrictedAdjoint_eq f U (A.unit.app M)
  have hi : (A.homEquiv _ _).symm (A.unit.app M) = 𝟙 _ := A.homEquiv_symm_unit M
  rw [hi, CategoryTheory.Functor.map_id] at h
  have he : (B.homEquiv _ _).symm φ = (localPullbackIso f U).inv.app M := by
    apply (cancel_epi ((localPullbackIso f U).hom.app M)).mp
    exact h.symm.trans (Iso.hom_inv_id_app (localPullbackIso f U) M).symm
  have hh := congrArg (B.homEquiv _ _) he
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit] at hh
  exact hh.symm
end AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local

namespace AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local
universe u
open AlgebraicGeometry.Scheme.Modules.Pullback.OpenRestriction
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
theorem restrictedPushforwardMap_apply (M : X.Modules) (W : U.toScheme.Opensᵒᵖ)
    (m : ((Scheme.Modules.restrictFunctor U.ι).obj
      ((Scheme.Modules.pushforward f).obj M)).val.obj W) :
    (restrictedPushforwardMap f U M).val.app W m =
      M.val.map (eqToHom (image_morphismRestrict_preimage f U W.unop)).op m := by
  exact congrArg (fun k ↦ k m) (restrictedPushforwardMap_app f U M W.unop)

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
end AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local

namespace AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local
universe u
open AlgebraicGeometry.Scheme.Modules.Pullback.OpenRestriction
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
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
end AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local

namespace AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local
universe u
open AlgebraicGeometry.Scheme.Modules.Pullback.OpenRestriction
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
/-- The canonical tensor comparison is invertible when the first factor is locally rank one. -/
theorem pullbackTensorMap_isIso (M N : Y.Modules) (hM : IsLocallyRankOne Y M) :
    IsIso (pullbackTensorMap f M N) := by
  apply isIso_of_local_restrict
  intro x
  obtain ⟨U, hxU, ⟨e⟩⟩ := (isLocallyRankOne_iff_restrict_unit M).mp hM (f.base x)
  refine ⟨f ⁻¹ᵁ U, hxU, ?_⟩
  haveI := pullbackTensorMap_isIso_of_trivial_left (f ∣_ U)
    ((Scheme.Modules.restrictFunctor U.ι).obj M)
    ((Scheme.Modules.restrictFunctor U.ι).obj N) e
  haveI := restrictTensorMap_isIso Y U M N
  haveI := restrictTensorMap_isIso X (f ⁻¹ᵁ U) ((Scheme.Modules.pullback f).obj M)
    ((Scheme.Modules.pullback f).obj N)
  haveI : IsIso (tensorSheafMap (f ⁻¹ᵁ U).toScheme
      ((localPullbackIso f U).inv.app M) ((localPullbackIso f U).inv.app N)) :=
    (tensorSheafIso (f ⁻¹ᵁ U).toScheme ((localPullbackIso f U).app M).symm
      ((localPullbackIso f U).app N).symm).isIso_hom
  haveI : IsIso ((Scheme.Modules.pullback (f ∣_ U)).map (restrictTensorMap Y U M N) ≫
      (localPullbackIso f U).inv.app (show Y.Modules from tensorSheaf Y M N) ≫
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map (pullbackTensorMap f M N)) := by
    rw [pullbackTensorMap_restrict]
    infer_instance
  haveI := IsIso.of_isIso_comp_left
    ((Scheme.Modules.pullback (f ∣_ U)).map (restrictTensorMap Y U M N))
    ((localPullbackIso f U).inv.app (show Y.Modules from tensorSheaf Y M N) ≫
      (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map (pullbackTensorMap f M N))
  exact IsIso.of_isIso_comp_left
    ((localPullbackIso f U).inv.app (show Y.Modules from tensorSheaf Y M N))
    ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).map (pullbackTensorMap f M N))

/-- The actual canonical pullback comparison for line bundles, with no tensor-pullback premise. -/
def pullbackLineBundleTensorIso (L M : LineBundle Y) :
    (pullbackLineBundle f (tensorLineBundle Y L M)).val ≅
      (tensorLineBundle X (pullbackLineBundle f L) (pullbackLineBundle f M)).val := by
  haveI := pullbackTensorMap_isIso f L.val M.val L.property
  let e := asIso (pullbackTensorMap f L.val M.val)
  exact ⟨e.hom, e.inv, e.hom_inv_id, e.inv_hom_id⟩

@[simp] theorem pullbackLineBundleTensorIso_hom (L M : LineBundle Y) :
    (pullbackLineBundleTensorIso f L M).hom = pullbackTensorMap f L.val M.val := rfl

theorem pullbackClass_add (a b : PicardGroup Y) :
    pullbackClass f (a + b) = pullbackClass f a + pullbackClass f b := by
  induction a using Quotient.inductionOn with | h L =>
    induction b using Quotient.inductionOn with | h M =>
      exact Quotient.sound ⟨pullbackLineBundleTensorIso f L M⟩

/-- Pullback on the actual Picard groups, proved from open-local unit charts. -/
def pullbackHom : PicardGroup Y →+ PicardGroup X where
  toFun := pullbackClass f
  map_zero' := pullbackClass_zero f
  map_add' := pullbackClass_add f

@[simp] theorem pullbackHom_apply (a : PicardGroup Y) :
    pullbackHom f a = pullbackClass f a := rfl

theorem pullbackClass_neg (a : PicardGroup Y) : pullbackClass f (-a) = -pullbackClass f a :=
  map_neg (pullbackHom f) a

@[simp] theorem pullbackHom_id :
    pullbackHom (𝟙 X) = AddMonoidHom.id (PicardGroup X) := by
  ext a
  exact pullbackClass_id a

@[simp] theorem pullbackHom_comp {Z : Scheme.{u}} (g : Y ⟶ Z) :
    pullbackHom (f ≫ g) = (pullbackHom f).comp (pullbackHom g) := by
  ext a
  exact pullbackClass_comp f g a
end AlgebraicGeometry.Scheme.Modules.Invertible.PullbackTensor.Local
