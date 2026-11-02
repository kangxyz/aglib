/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.TensorAdjunction
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Restriction
public import Aglib.Algebra.Category.ModuleCat.Sheaf.Pullback.Tensor

/-!
# Tensor pullback for arbitrary module sheaves

The generic tensor-Hom universal property and the actual restricted pullback adjunction
construct an explicit inverse to the existing canonical `pullbackTensorMap`.
Both inverse equations retain arbitrary schemes, morphisms and module sheaves;
no quasicoherence, flatness, finiteness or rank hypothesis is used.

Source: `R5Lab/AlgebraicGeometry/Curves/Picard/PullbackTensor/Isomorphism.lean` at frozen R5
  integration
`79307ff88f07d34fd5c3edb859f799c55e38f290`,
SHA-256 `1e43c9e95fcda1d593dca143445b8cd32006d2aa8388dc23c50b021647e7a33b`.
The source proof constructs the inverse rather than importing an external
proof. Its statement corresponds to Stacks Project tag 01CD.
-/

@[expose] public section

open AlgebraicGeometry.Scheme.Modules
  (pullbackTensorMap pullbackTensorMap_adjoint pushforwardTensorMap pushforwardTensorMap_tmul
    tensorSheaf tensorSheafMap tensorSheafMap_tmul tensorSheafUnit)
open AlgebraicGeometry.Scheme.Modules.Pullback.OpenRestriction
  (localPullbackIso restrictedPushforwardIso restrictedPushforwardMap
    restrictedPushforwardMap_apply restrictedUnit)

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules.Pullback.Tensor
universe u
variable (X : Scheme.{u}) (M N P : X.Modules)

/-- The original currying section, from the actual generic tensor–Hom constructor. -/
abbrev currySection (h : tensorSheaf X M N ⟶ P) (U : X.Opensᵒᵖ) (m : M.val.obj U) :
    (_root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X N P).val.obj U :=
  _root_.SheafOfModules.InternalHom.currySection.{u, u, u}
    (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf M N P h U m

/-- The original currying morphism, from the actual generic tensor–Hom constructor. -/
abbrev curry (h : tensorSheaf X M N ⟶ P) : M ⟶
    _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X N P :=
  _root_.SheafOfModules.InternalHom.curry.{u, u, u}
    (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf M N P h

/-- The original presheaf uncurrying map, from the actual generic constructor. -/
abbrev uncurryPresheaf
    (h : M ⟶ _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X N P) :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val ⟶ P.val :=
  _root_.SheafOfModules.InternalHom.uncurryPresheaf.{u, u, u}
    (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf M N P h

/-- The original uncurrying morphism uses the same native sheafification map. -/
abbrev uncurry (h : M ⟶ _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X N P) :
    tensorSheaf X M N ⟶ P :=
  _root_.SheafOfModules.InternalHom.uncurry.{u, u, u}
    (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf M N P h

/-- The original pure-section formula for the actual uncurrying morphism. -/
theorem uncurry_tmul
    (h : M ⟶ _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X N P)
    (U : X.Opensᵒᵖ) (m : M.val.obj U) (n : N.val.obj U) :
    (uncurry X M N P h).val.app U ((tensorSheafUnit X M N).app U (m ⊗ₜ n)) =
      (h.val.app U m).val.app (op (Over.mk (𝟙 U.unop))) n :=
  _root_.SheafOfModules.InternalHom.uncurry_tmul.{u, u, u}
    (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf M N P h U m n

theorem uncurry_curry (h : tensorSheaf X M N ⟶ P) :
    uncurry X M N P (curry X M N P h) = h :=
  _root_.SheafOfModules.InternalHom.uncurry_curry.{u, u, u}
    (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf M N P h

theorem curry_uncurry
    (h : M ⟶ _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X N P) :
    curry X M N P (uncurry X M N P h) = h :=
  _root_.SheafOfModules.InternalHom.curry_uncurry.{u, u, u}
    (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf M N P h

/-- The original tensor/internal-Hom equivalence is the actual generic equivalence. -/
abbrev tensorHomEquiv :
    (tensorSheaf X M N ⟶ P) ≃
      (M ⟶ _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X N P) :=
  _root_.SheafOfModules.InternalHom.tensorHomEquiv.{u, u, u}
    (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf M N P

/-- The whole original currying map is the actual generic map on the same arrow. -/
theorem curry_eq_generic (h : tensorSheaf X M N ⟶ P) :
    curry X M N P h =
      _root_.SheafOfModules.InternalHom.curry.{u, u, u}
        (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf M N P h := rfl

/-- The whole original uncurrying map is the actual generic map on the same arrow. -/
theorem uncurry_eq_generic
    (h : M ⟶ _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X N P) :
    uncurry X M N P h =
      _root_.SheafOfModules.InternalHom.uncurry.{u, u, u}
        (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf M N P h := rfl

/-- The whole original equivalence is the actual generic equivalence on the same tensor. -/
theorem tensorHomEquiv_eq_generic :
    tensorHomEquiv X M N P =
      _root_.SheafOfModules.InternalHom.tensorHomEquiv.{u, u, u}
        (C := X.Opens) (J := Opens.grothendieckTopology X) X.sheaf M N P := rfl

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (N : Y.Modules) (P : X.Modules)

local instance preimageOverContinuous : ∀ U : Y.Opens,
    (Over.post (Opens.map f.base)).IsContinuous
      ((Opens.grothendieckTopology Y).over U)
      ((Opens.grothendieckTopology X).over (f ⁻¹ᵁ U)) :=
  fun U ↦ _root_.SheafOfModules.Pullback.overPost_isContinuous
    (F := Opens.map f.base) (J := Opens.grothendieckTopology Y)
    (K := Opens.grothendieckTopology X) U

local instance preimageOverPushforwardRightAdjoint : ∀ U : Y.Opens,
    (SheafOfModules.pushforward.{u}
      (_root_.SheafOfModules.Pullback.restrictedRingHom
        (_root_.SheafOfModules.Pullback.ringHom
          (F := Opens.map f.base) (S := Y.sheaf) (R := X.sheaf) ⟨f.c⟩) U)).IsRightAdjoint :=
  fun _ ↦ inferInstance


/-- The inverse-image functor between over-categories of opens. -/
def preimageOverFunctor (U : Y.Opens) : Over U ⥤ Over (f ⁻¹ᵁ U) where
  obj V := Over.mk ((TopologicalSpace.Opens.map f.base).map V.hom)
  map i := Over.homMk ((TopologicalSpace.Opens.map f.base).map i.left)

/-- The internal-Hom map on sections induced by the pullback adjunction. -/
def pushforwardHomSection (U : Y.Opensᵒᵖ)
    (s : (_root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X ((Scheme.Modules.pullback
      f).obj N) P).val.obj
      (op (f ⁻¹ᵁ U.unop))) :
    (_root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf Y N ((Scheme.Modules.pushforward
      f).obj P)).val.obj U :=
  _root_.SheafOfModules.Pullback.pushforwardHomSection.{u, u, u, u, u, u}
    (F := Opens.map f.base) (S := Y.sheaf) (R := X.sheaf) ⟨f.c⟩ N P U s

/-- The direct-image/internal-Hom comparison with the pulled-back first argument. -/
def pushforwardHomMap :
    (Scheme.Modules.pushforward f).obj
      (_root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X ((Scheme.Modules.pullback
        f).obj N) P) ⟶
    _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf Y N ((Scheme.Modules.pushforward
      f).obj P) :=
  _root_.SheafOfModules.Pullback.pushforwardHomMap.{u, u, u, u, u, u}
    (F := Opens.map f.base) (S := Y.sheaf) (R := X.sheaf) ⟨f.c⟩ N P

variable (X : Scheme.{u}) (M N : X.Modules)
/-- Internal-Hom sections over an open as arrows between restricted modules. -/
def restrictedHomEquiv (U : X.Opens) :
    (_root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X M N).val.obj (op U) ≃
      ((Scheme.Modules.restrictFunctor U.ι).obj M ⟶
        (Scheme.Modules.restrictFunctor U.ι).obj N) :=
  (_root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sectionHomEquiv X M N U).trans
    ((Scheme.Modules.overEquiv U).fullyFaithfulFunctor.homEquiv.trans
      (Iso.homCongr ((Scheme.Modules.overFunctorEquiv U).app M)
        ((Scheme.Modules.overFunctorEquiv U).app N)))

theorem restrictedHomEquiv_apply (U : X.Opens)
    (s : (_root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X M N).val.obj (op U))
    (V : U.toScheme.Opensᵒᵖ) (m : M.val.obj (op (U.ι ''ᵁ V.unop))) :
    (restrictedHomEquiv X M N U s).val.app V m =
      s.val.app (op (Over.mk (homOfLE (U.ι_image_le V.unop)))) m := by
  rfl


variable {X Y : Scheme.{u}} (f : X ⟶ Y) (N : Y.Modules) (P : X.Modules)
theorem pushforwardHomSection_adjoint (U : Y.Opens)
    (s : (_root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X ((Scheme.Modules.pullback
      f).obj N) P).val.obj
      (op (f ⁻¹ᵁ U))) :
    (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _
      ((localPullbackIso f U).inv.app N ≫
        restrictedHomEquiv X ((Scheme.Modules.pullback f).obj N) P (f ⁻¹ᵁ U) s) =
      restrictedHomEquiv Y N ((Scheme.Modules.pushforward f).obj P) U
        (pushforwardHomSection f N P (op U) s) ≫ restrictedPushforwardMap f U P := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, restrictedUnit]
  apply SheafOfModules.hom_ext
  ext V : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  change (restrictedHomEquiv X ((Scheme.Modules.pullback f).obj N) P (f ⁻¹ᵁ U) s).val.app
      (op ((f ∣_ U) ⁻¹ᵁ V.unop))
        ((restrictedPushforwardMap f U ((Scheme.Modules.pullback f).obj N)).val.app V
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app
            (op (U.ι ''ᵁ V.unop)) m)) =
    (restrictedPushforwardMap f U P).val.app V
      ((restrictedHomEquiv Y N ((Scheme.Modules.pushforward f).obj P) U
        (pushforwardHomSection f N P (op U) s)).val.app V m)
  rw [restrictedHomEquiv_apply, restrictedHomEquiv_apply,
    restrictedPushforwardMap_apply, restrictedPushforwardMap_apply]
  let T : Over (f ⁻¹ᵁ U) := Over.mk
    (homOfLE ((f ⁻¹ᵁ U).ι_image_le ((f ∣_ U) ⁻¹ᵁ V.unop)))
  let W : Over U := Over.mk (homOfLE (U.ι_image_le V.unop))
  let i : T ⟶ (preimageOverFunctor f U).obj W :=
    Over.homMk (eqToHom (image_morphismRestrict_preimage f U V.unop))
  exact NatTrans.naturality_apply s.val i.op
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app
      (op (U.ι ''ᵁ V.unop)) m)

/-- The adjunction over an open, expressed as internal-Hom sections. -/
def pullbackHomSectionsEquiv (U : Y.Opens) :
    (_root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X ((Scheme.Modules.pullback f).obj
      N) P).val.obj (op (f ⁻¹ᵁ U)) ≃
      (_root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf Y N ((Scheme.Modules.pushforward
        f).obj P)).val.obj (op U) :=
  (restrictedHomEquiv X ((Scheme.Modules.pullback f).obj N) P (f ⁻¹ᵁ U)).trans
    ((Iso.homCongr ((localPullbackIso f U).app N) (Iso.refl _)).trans
      (((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _).trans
        ((Iso.homCongr (Iso.refl _) (restrictedPushforwardIso f U P).symm).trans
          (restrictedHomEquiv Y N ((Scheme.Modules.pushforward f).obj P) U).symm)))

theorem pullbackHomSectionsEquiv_apply (U : Y.Opens)
    (s : (_root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X ((Scheme.Modules.pullback
      f).obj N) P).val.obj (op (f ⁻¹ᵁ U))) :
    pullbackHomSectionsEquiv f N P U s = pushforwardHomSection f N P (op U) s := by
  apply (restrictedHomEquiv Y N ((Scheme.Modules.pushforward f).obj P) U).injective
  simp only [pullbackHomSectionsEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    Iso.homCongr_apply, Iso.refl_inv, Iso.symm_hom, Category.id_comp]
  change (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).homEquiv _ _
      ((localPullbackIso f U).inv.app N ≫
        restrictedHomEquiv X ((Scheme.Modules.pullback f).obj N) P (f ⁻¹ᵁ U) s) ≫
      (restrictedPushforwardIso f U P).inv = _
  rw [pushforwardHomSection_adjoint]
  change (_ ≫ (restrictedPushforwardIso f U P).hom) ≫
    (restrictedPushforwardIso f U P).inv = _
  simp

/-- The original open-subscheme equivalence is the generic native slice equivalence. -/
theorem pullbackHomSectionsEquiv_eq_generic (U : Y.Opens) :
    pullbackHomSectionsEquiv f N P U =
      _root_.SheafOfModules.Pullback.pullbackHomSectionsEquiv.{u, u, u, u, u, u}
        (F := Opens.map f.base) (S := Y.sheaf) (R := X.sheaf) ⟨f.c⟩ N P U := by
  apply Equiv.ext
  intro s
  exact (pullbackHomSectionsEquiv_apply f N P U s).trans
    (_root_.SheafOfModules.Pullback.pullbackHomSectionsEquiv_apply.{u, u, u, u, u, u}
      (F := Opens.map f.base) (S := Y.sheaf) (R := X.sheaf) ⟨f.c⟩ N P U s).symm

theorem pushforwardHomMap_isIso : IsIso (pushforwardHomMap f N P) :=
  _root_.SheafOfModules.Pullback.pushforwardHomMap_isIso.{u, u, u, u, u, u}
    (F := Opens.map f.base) (S := Y.sheaf) (R := X.sheaf) ⟨f.c⟩ N P

/-- The direct-image/internal-Hom isomorphism from the actual section equivalences. -/
def pushforwardHomIso :
    (Scheme.Modules.pushforward f).obj
      (_root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X ((Scheme.Modules.pullback
        f).obj N) P) ≅
    _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf Y N ((Scheme.Modules.pushforward
      f).obj P) :=
  _root_.SheafOfModules.Pullback.pushforwardHomIso.{u, u, u, u, u, u}
    (F := Opens.map f.base) (S := Y.sheaf) (R := X.sheaf) ⟨f.c⟩ N P

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
/-- The literal original Scheme tensor arrow is the generic native adjunction arrow. -/
theorem pullbackTensorMap_eq_generic (M N : Y.Modules) :
    pullbackTensorMap f M N =
      _root_.SheafOfModules.Pullback.Tensor.pullbackTensorMap.{u, u, u, u, u}
        (F := Opens.map f.base) (S := Y.sheaf) (R := X.sheaf) ⟨f.c⟩ M N := rfl

theorem curry_pullback_adjoint (M N : Y.Modules) (P : X.Modules)
    (g : tensorSheaf X ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N) ⟶ P) :
    curry Y M N ((Scheme.Modules.pushforward f).obj P)
      (tensorSheafMap Y ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) ≫
        pushforwardTensorMap f ((Scheme.Modules.pullback f).obj M)
          ((Scheme.Modules.pullback f).obj N) ≫ (Scheme.Modules.pushforward f).map g) =
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
      (Scheme.Modules.pushforward f).map
        (curry X ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) P g) ≫
      pushforwardHomMap f N P :=
  _root_.SheafOfModules.Pullback.Tensor.curry_pullback_adjoint.{u, u, u, u, u}
    (F := Opens.map f.base) (S := Y.sheaf) (R := X.sheaf) ⟨f.c⟩ M N P g

/-- The tensor pullback equivalence induced by currying and the actual adjunction. -/
def tensorPullbackHomEquiv (M N : Y.Modules) (P : X.Modules) :
    (tensorSheaf X ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N) ⟶ P) ≃
    ((Scheme.Modules.pullback f).obj (tensorSheaf Y M N) ⟶ P) :=
  _root_.SheafOfModules.Pullback.Tensor.tensorPullbackHomEquiv.{u, u, u, u, u}
    (F := Opens.map f.base) (S := Y.sheaf) (R := X.sheaf) ⟨f.c⟩ M N P

theorem tensorPullbackHomEquiv_apply (M N : Y.Modules) (P : X.Modules)
    (g : tensorSheaf X ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N) ⟶ P) :
    tensorPullbackHomEquiv f M N P g = pullbackTensorMap f M N ≫ g := by
  rw [pullbackTensorMap_eq_generic]
  exact _root_.SheafOfModules.Pullback.Tensor.tensorPullbackHomEquiv_apply.{u, u, u, u, u}
    (F := Opens.map f.base) (S := Y.sheaf) (R := X.sheaf) ⟨f.c⟩ M N P g

/-- The inverse is obtained from the bilinear universal property and the actual pullback
  adjunction. -/
def pullbackTensorInverse (M N : Y.Modules) :
    tensorSheaf X ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N) ⟶
    (Scheme.Modules.pullback f).obj (tensorSheaf Y M N) :=
  _root_.SheafOfModules.Pullback.Tensor.pullbackTensorInverse.{u, u, u, u, u}
    (F := Opens.map f.base) (S := Y.sheaf) (R := X.sheaf) ⟨f.c⟩ M N

theorem pullbackTensorMap_inverse (M N : Y.Modules) :
    pullbackTensorMap f M N ≫ pullbackTensorInverse f M N = 𝟙 _ := by
  rw [pullbackTensorMap_eq_generic]
  exact _root_.SheafOfModules.Pullback.Tensor.pullbackTensorMap_inverse.{u, u, u, u, u}
    (F := Opens.map f.base) (S := Y.sheaf) (R := X.sheaf) ⟨f.c⟩ M N

theorem pullbackTensorInverse_map (M N : Y.Modules) :
    pullbackTensorInverse f M N ≫ pullbackTensorMap f M N = 𝟙 _ := by
  rw [pullbackTensorMap_eq_generic]
  exact _root_.SheafOfModules.Pullback.Tensor.pullbackTensorInverse_map.{u, u, u, u, u}
    (F := Opens.map f.base) (S := Y.sheaf) (R := X.sheaf) ⟨f.c⟩ M N

theorem pullbackTensorMap_isIso (M N : Y.Modules) : IsIso (pullbackTensorMap f M N) := by
  rw [pullbackTensorMap_eq_generic]
  exact _root_.SheafOfModules.Pullback.Tensor.pullbackTensorMap_isIso.{u, u, u, u, u}
    (F := Opens.map f.base) (S := Y.sheaf) (R := X.sheaf) ⟨f.c⟩ M N

end AlgebraicGeometry.Scheme.Modules.Pullback.Tensor
