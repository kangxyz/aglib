/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.InternalHom
public import Aglib.AlgebraicGeometry.Modules.Pullback.Tensor.Restriction

/-!
# Tensor pullback for arbitrary module sheaves

The tensor-Hom universal property and the actual restricted pullback adjunction
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

/-- Currying a tensor arrow on sections over the over-category of an open. -/
def currySection (h : tensorSheaf X M N ⟶ P) (U : X.Opensᵒᵖ) (m : M.val.obj U) :
    (_root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X N P).val.obj U :=
  ⟨{
    app V := AddCommGrpCat.ofHom {
      toFun n := h.val.app (op V.unop.left)
        ((tensorSheafUnit X M N).app (op V.unop.left)
          (M.val.map V.unop.hom.op m ⊗ₜ n))
      map_zero' := by simp
      map_add' n n' := by simp [TensorProduct.tmul_add] }
    naturality {V W} i := by
      ext n
      change h.val.app (op W.unop.left)
        ((tensorSheafUnit X M N).app (op W.unop.left)
          (M.val.map W.unop.hom.op m ⊗ₜ N.val.map i.unop.left.op n)) =
        P.val.map i.unop.left.op
          (h.val.app (op V.unop.left)
            ((tensorSheafUnit X M N).app (op V.unop.left)
              (M.val.map V.unop.hom.op m ⊗ₜ n)))
      rw [← PresheafOfModules.naturality_apply]
      have ht := PresheafOfModules.naturality_apply (tensorSheafUnit X M N)
        i.unop.left.op (M.val.map V.unop.hom.op m ⊗ₜ n)
      change (tensorSheafUnit X M N).app (op W.unop.left)
        (M.val.map i.unop.left.op (M.val.map V.unop.hom.op m) ⊗ₜ
          N.val.map i.unop.left.op n) = _ at ht
      rw [← M.val.map_comp_apply, ← op_comp, Over.w i.unop] at ht
      exact congrArg (h.val.app (op W.unop.left)) ht
  }, by
    intro V r n
    change h.val.app (op V.unop.left)
      ((tensorSheafUnit X M N).app (op V.unop.left)
        (M.val.map V.unop.hom.op m ⊗ₜ (r • n))) =
      r • h.val.app (op V.unop.left)
        ((tensorSheafUnit X M N).app (op V.unop.left)
          (M.val.map V.unop.hom.op m ⊗ₜ n))
    rw [TensorProduct.tmul_smul, _root_.map_smul, _root_.map_smul]⟩

/-- Currying a tensor arrow as a morphism into internal Hom. -/
def curry (h : tensorSheaf X M N ⟶ P) : M ⟶
  _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X N P where
  val.app U := ModuleCat.ofHom {
    toFun := currySection X M N P h U
    map_add' m m' := by
      apply Subtype.ext
      change (_ : _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.RawHom X N P U.unop) = _
      ext V n
      change h.val.app (op V.unop.left) ((tensorSheafUnit X M N).app (op V.unop.left)
        (M.val.map V.unop.hom.op (m + m') ⊗ₜ n)) = _
      rw [map_add, TensorProduct.add_tmul, map_add, map_add]
      rfl
    map_smul' r m := by
      apply Subtype.ext
      change (_ : _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.RawHom X N P U.unop) = _
      ext V n
      change h.val.app (op V.unop.left) ((tensorSheafUnit X M N).app (op V.unop.left)
        (M.val.map V.unop.hom.op (r • m) ⊗ₜ n)) =
        X.presheaf.map V.unop.hom.op r •
          h.val.app (op V.unop.left) ((tensorSheafUnit X M N).app (op V.unop.left)
            (M.val.map V.unop.hom.op m ⊗ₜ n))
      rw [M.val.map_smul]
      change h.val.app (op V.unop.left) ((tensorSheafUnit X M N).app (op V.unop.left)
        ((X.presheaf.map V.unop.hom.op r • M.val.map V.unop.hom.op m) ⊗ₜ n)) = _
      have ht := (TensorProduct.smul_tmul' (R := Γ(X, V.unop.left))
        (X.presheaf.map V.unop.hom.op r)
        (M.val.map V.unop.hom.op m : M.val.obj (op V.unop.left))
        (n : N.val.obj (op V.unop.left))).symm
      have hu := ((tensorSheafUnit X M N).app (op V.unop.left)).hom.map_smul
        (X.presheaf.map V.unop.hom.op r) (M.val.map V.unop.hom.op m ⊗ₜ n)
      have hh := (h.val.app (op V.unop.left)).hom.map_smul
        (X.presheaf.map V.unop.hom.op r)
        ((tensorSheafUnit X M N).app (op V.unop.left) (M.val.map V.unop.hom.op m ⊗ₜ n))
      exact (congrArg (fun z ↦ h.val.app (op V.unop.left)
        ((tensorSheafUnit X M N).app (op V.unop.left) z)) ht).trans
          ((congrArg (h.val.app (op V.unop.left)) hu).trans hh) }
  val.naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    apply Subtype.ext
    change (_ : _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.RawHom X N P V.unop) = _
    ext W n
    change h.val.app (op W.unop.left) ((tensorSheafUnit X M N).app (op W.unop.left)
      (M.val.map W.unop.hom.op (M.val.map i m) ⊗ₜ n)) =
      h.val.app (op W.unop.left) ((tensorSheafUnit X M N).app (op W.unop.left)
        (M.val.map ((Over.map i.unop).obj W.unop).hom.op m ⊗ₜ n))
    rw [← M.val.map_comp_apply]
    rfl

/-- The presheaf arrow evaluating an internal-Hom morphism on tensor generators. -/
def uncurryPresheaf (h : M ⟶ _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X N P) :
    PresheafOfModulesOfCommRing.Monoidal.tensorObj (R := X.presheaf) M.val N.val ⟶ P.val :=
  PresheafOfModulesOfCommRing.homMk (fun U ↦
      ModuleCat.MonoidalCategory.tensorLift
        (fun m n ↦ (h.val.app U m).val.app (op (Over.mk (𝟙 U.unop))) n)
        (by intro m m' n; rw [map_add]; rfl)
        (by
          intro r m n
          rw [(h.val.app U).hom.map_smul]
          change X.presheaf.map (𝟙 U.unop).op r •
            (show P.val.obj U from (h.val.app U m).val.app (op (Over.mk (𝟙 U.unop))) n) = _
          simp)
        (by intro m n n'; exact ((h.val.app U m).val.app _).hom.map_add _ _)
        (by intro r m n; exact (h.val.app U m).property (op (Over.mk (𝟙 U.unop))) r n))
      (by
        intro U V i
        apply ModuleCat.MonoidalCategory.tensor_ext
        intro m n
        have hh := PresheafOfModules.naturality_apply h.val i m
        have hn := NatTrans.naturality_apply (h.val.app U m).val
          (Over.homMk i.unop : Over.mk i.unop ⟶ Over.mk (𝟙 U.unop)).op n
        change (h.val.app V (M.val.map i m)).val.app (op (Over.mk (𝟙 V.unop)))
          (N.val.map i n) = P.val.map i ((h.val.app U m).val.app (op (Over.mk (𝟙 U.unop))) n)
        rw [hh]
        exact hn)

/-- Uncurrying an internal-Hom morphism through module sheafification. -/
def uncurry (h : M ⟶ _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X N P) :
  tensorSheaf X M N ⟶ P :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).symm
    (uncurryPresheaf X M N P h)

theorem uncurry_tmul (h : M ⟶ _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X N P) (U
  : X.Opensᵒᵖ)
    (m : M.val.obj U) (n : N.val.obj U) :
    (uncurry X M N P h).val.app U ((tensorSheafUnit X M N).app U (m ⊗ₜ n)) =
      (h.val.app U m).val.app (op (Over.mk (𝟙 U.unop))) n := by
  have hh := (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).apply_symm_apply
    (uncurryPresheaf X M N P h)
  exact congrArg (fun k ↦ k.app U (m ⊗ₜ n)) hh

theorem uncurry_curry (h : tensorSheaf X M N ⟶ P) :
    uncurry X M N P (curry X M N P h) = h := by
  apply (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).injective
  ext U : 1
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro m n
  change (uncurry X M N P (curry X M N P h)).val.app U
    ((tensorSheafUnit X M N).app U (m ⊗ₜ n)) = _
  rw [uncurry_tmul]
  change h.val.app U ((tensorSheafUnit X M N).app U (M.val.map (𝟙 U.unop).op m ⊗ₜ n)) =
    h.val.app U ((tensorSheafUnit X M N).app U (m ⊗ₜ n))
  have hi := ConcreteCategory.congr_hom (M.val.presheaf.map_id U) m
  change M.val.map (𝟙 U) m = m at hi
  rw [show (𝟙 U.unop).op = 𝟙 U from rfl, hi]

theorem curry_uncurry (h : M ⟶ _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X N P) :
    curry X M N P (uncurry X M N P h) = h := by
  apply SheafOfModules.hom_ext
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  change (_ : _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.RawHom X N P U.unop) = _
  ext V n
  change (uncurry X M N P h).val.app (op V.unop.left)
    ((tensorSheafUnit X M N).app (op V.unop.left)
      (M.val.map V.unop.hom.op m ⊗ₜ n)) = (h.val.app U m).val.app V n
  rw [uncurry_tmul, PresheafOfModules.naturality_apply]
  rfl

/-- The tensor/internal-Hom equivalence on the actual module-sheaf arrows. -/
def tensorHomEquiv :
    (tensorSheaf X M N ⟶ P) ≃ (M ⟶ _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X N
      P) where
  toFun := curry X M N P
  invFun := uncurry X M N P
  left_inv := uncurry_curry X M N P
  right_inv := curry_uncurry X M N P

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (N : Y.Modules) (P : X.Modules)

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
  ⟨{
    app V := AddCommGrpCat.ofHom <|
      ((s.val.app ((preimageOverFunctor f U.unop).op.obj V)).hom).comp
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app
          (op V.unop.left)).hom.toAddMonoidHom
    naturality {V W} i := by
      ext m
      change s.val.app ((preimageOverFunctor f U.unop).op.obj W)
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app
          (op W.unop.left) (N.val.map i.unop.left.op m)) =
        P.val.map ((Opens.map f.base).map i.unop.left).op
          (s.val.app ((preimageOverFunctor f U.unop).op.obj V)
            (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app
              (op V.unop.left) m))
      have hu := PresheafOfModules.naturality_apply
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val i.unop.left.op m
      have hs := NatTrans.naturality_apply s.val
        ((preimageOverFunctor f U.unop).map i.unop).op
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app (op V.unop.left) m)
      exact (congrArg (s.val.app ((preimageOverFunctor f U.unop).op.obj W)) hu).trans hs
  }, by
    intro V r m
    have hu := (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app
      (op V.unop.left)).hom.map_smul r m
    have hs := s.property ((preimageOverFunctor f U.unop).op.obj V) (f.app V.unop.left r)
      (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app (op V.unop.left) m)
    exact (congrArg (s.val.app ((preimageOverFunctor f U.unop).op.obj V)) hu).trans hs⟩

/-- The direct-image/internal-Hom comparison with the pulled-back first argument. -/
def pushforwardHomMap :
    (Scheme.Modules.pushforward f).obj
      (_root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X ((Scheme.Modules.pullback
        f).obj N) P) ⟶
    _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf Y N ((Scheme.Modules.pushforward
      f).obj P) where
  val.app U := ModuleCat.ofHom
    (X := ((Scheme.Modules.pushforward f).obj
      (_root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X ((Scheme.Modules.pullback
        f).obj N) P)).val.obj U)
    (Y := (_root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf Y N
      ((Scheme.Modules.pushforward f).obj P)).val.obj U) {
    toFun := pushforwardHomSection f N P U
    map_add' s t := by
      apply Subtype.ext
      change (_ : _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.RawHom Y N
        ((Scheme.Modules.pushforward f).obj P) U.unop) = _
      ext V m
      rfl
    map_smul' r s := by
      apply Subtype.ext
      change (_ : _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.RawHom Y N
        ((Scheme.Modules.pushforward f).obj P) U.unop) = _
      ext V m
      change X.presheaf.map ((Opens.map f.base).map V.unop.hom).op
          (f.app U.unop r) •
          (show P.val.obj (op (f ⁻¹ᵁ V.unop.left)) from
            s.val.app ((preimageOverFunctor f U.unop).op.obj V)
              (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app _ m)) =
        f.app V.unop.left (Y.presheaf.map V.unop.hom.op r) •
          (show P.val.obj (op (f ⁻¹ᵁ V.unop.left)) from
            s.val.app ((preimageOverFunctor f U.unop).op.obj V)
              (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app _ m))
      congr 1
      exact (ConcreteCategory.congr_hom (f.naturality V.unop.hom.op) r).symm }
  val.naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply Subtype.ext
    change (_ : _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.RawHom Y N
      ((Scheme.Modules.pushforward f).obj P) V.unop) = _
    ext W m
    rfl

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

theorem pushforwardHomMap_isIso : IsIso (pushforwardHomMap f N P) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  convert (pullbackHomSectionsEquiv f N P U).bijective using 1
  funext s
  exact (pullbackHomSectionsEquiv_apply f N P U s).symm

/-- The direct-image/internal-Hom isomorphism from the actual section equivalences. -/
def pushforwardHomIso :
    (Scheme.Modules.pushforward f).obj
      (_root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf X ((Scheme.Modules.pullback
        f).obj N) P) ≅
    _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.sheaf Y N ((Scheme.Modules.pushforward
      f).obj P) := by
  haveI := pushforwardHomMap_isIso f N P
  exact asIso (pushforwardHomMap f N P)


variable {X Y : Scheme.{u}} (f : X ⟶ Y)
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
      pushforwardHomMap f N P := by
  apply SheafOfModules.hom_ext
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  change (_ : _root_.AlgebraicGeometry.Scheme.Modules.InternalHom.RawHom Y N
    ((Scheme.Modules.pushforward f).obj P) U.unop) = _
  ext V n
  change g.val.app (op (f ⁻¹ᵁ V.unop.left))
    ((pushforwardTensorMap f ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N)).val.app (op V.unop.left)
      ((tensorSheafMap Y ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N)).val.app (op V.unop.left)
        ((tensorSheafUnit Y M N).app (op V.unop.left)
          (M.val.map V.unop.hom.op m ⊗ₜ n)))) =
    g.val.app (op (f ⁻¹ᵁ V.unop.left))
      ((tensorSheafUnit X ((Scheme.Modules.pullback f).obj M)
        ((Scheme.Modules.pullback f).obj N)).app (op (f ⁻¹ᵁ V.unop.left))
        (((Scheme.Modules.pullback f).obj M).val.map
          ((Opens.map f.base).map V.unop.hom).op
          (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app U m) ⊗ₜ
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app (op V.unop.left) n))
  have h₁ := tensorSheafMap_tmul Y
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M)
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N) (op V.unop.left)
    (M.val.map V.unop.hom.op m : M.val.obj (op V.unop.left)) n
  have h₂ := pushforwardTensorMap_tmul f ((Scheme.Modules.pullback f).obj M)
    ((Scheme.Modules.pullback f).obj N) (op V.unop.left)
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app
      (op V.unop.left) (M.val.map V.unop.hom.op m))
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app (op V.unop.left) n)
  have he := congrArg (g.val.app (op (f ⁻¹ᵁ V.unop.left)))
    ((congrArg ((pushforwardTensorMap f ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N)).val.app (op V.unop.left)) h₁).trans h₂)
  have hu := PresheafOfModules.naturality_apply
    ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val V.unop.hom.op m
  exact he.trans (congrArg (fun z ↦ g.val.app (op (f ⁻¹ᵁ V.unop.left))
    ((tensorSheafUnit X ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N)).app (op (f ⁻¹ᵁ V.unop.left))
      (z ⊗ₜ ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app N).val.app
        (op V.unop.left) n))) hu)

/-- The tensor pullback equivalence induced by currying and the actual adjunction. -/
def tensorPullbackHomEquiv (M N : Y.Modules) (P : X.Modules) :
    (tensorSheaf X ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N) ⟶ P) ≃
    ((Scheme.Modules.pullback f).obj (tensorSheaf Y M N) ⟶ P) :=
  (tensorHomEquiv X ((Scheme.Modules.pullback f).obj M)
    ((Scheme.Modules.pullback f).obj N) P).trans
    (((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).trans
      ((Iso.homCongr (Iso.refl M) (pushforwardHomIso f N P)).trans
        ((tensorHomEquiv Y M N ((Scheme.Modules.pushforward f).obj P)).symm.trans
          ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm)))

theorem tensorPullbackHomEquiv_apply (M N : Y.Modules) (P : X.Modules)
    (g : tensorSheaf X ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N) ⟶ P) :
    tensorPullbackHomEquiv f M N P g = pullbackTensorMap f M N ≫ g := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  simp only [tensorPullbackHomEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  apply (tensorHomEquiv Y M N ((Scheme.Modules.pushforward f).obj P)).injective
  rw [Equiv.apply_symm_apply]
  change (Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
      (curry X ((Scheme.Modules.pullback f).obj M) ((Scheme.Modules.pullback f).obj N) P g) ≫
      pushforwardHomMap f N P =
    curry Y M N ((Scheme.Modules.pushforward f).obj P)
      ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _ (pullbackTensorMap f M N ≫ g))
  rw [Adjunction.homEquiv_naturality_right, pullbackTensorMap_adjoint,
    Adjunction.homEquiv_unit]
  exact (curry_pullback_adjoint f M N P g).symm

/-- The inverse is obtained from the bilinear universal property and the actual pullback
  adjunction. -/
def pullbackTensorInverse (M N : Y.Modules) :
    tensorSheaf X ((Scheme.Modules.pullback f).obj M)
      ((Scheme.Modules.pullback f).obj N) ⟶
    (Scheme.Modules.pullback f).obj (tensorSheaf Y M N) :=
  (tensorPullbackHomEquiv f M N _).symm (𝟙 _)

theorem pullbackTensorMap_inverse (M N : Y.Modules) :
    pullbackTensorMap f M N ≫ pullbackTensorInverse f M N = 𝟙 _ := by
  rw [← tensorPullbackHomEquiv_apply]
  exact (tensorPullbackHomEquiv f M N _).apply_symm_apply (𝟙 _)

theorem pullbackTensorInverse_map (M N : Y.Modules) :
    pullbackTensorInverse f M N ≫ pullbackTensorMap f M N = 𝟙 _ := by
  apply (tensorPullbackHomEquiv f M N _).injective
  rw [tensorPullbackHomEquiv_apply, tensorPullbackHomEquiv_apply,
    ← Category.assoc, pullbackTensorMap_inverse, Category.id_comp, Category.comp_id]

theorem pullbackTensorMap_isIso (M N : Y.Modules) : IsIso (pullbackTensorMap f M N) :=
  ⟨⟨pullbackTensorInverse f M N, pullbackTensorMap_inverse f M N,
    pullbackTensorInverse_map f M N⟩⟩

end AlgebraicGeometry.Scheme.Modules.Pullback.Tensor
