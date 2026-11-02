/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Pullback.Hom
public import Aglib.Algebra.Category.ModuleCat.Sheaf.InternalHom.TensorAdjunction
public import Aglib.Algebra.Category.ModuleCat.Sheaf.TensorPushforwardMap

/-!
# The canonical binary tensor comparison for native module pullback

The inverse is constructed from the actual tensor–Hom and pullback adjunctions.
The defining equivalence is proved to act by precomposition with the original
unit-induced tensor arrow. Product and slice hypotheses are used to prove the
actual Hom comparison invertible; no comparison isomorphism is an input.
-/

@[expose] public section

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModulesOfCommRing (tensorProduct tensorMap tensorUnitMap tensorSection)

universe uC vC uD vD r

namespace SheafOfModules.Pullback.Tensor

variable {C : Type uC} {D : Type uD} [Category.{vC} C] [Category.{vD} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose
    (forget₂ CommRingCat.{max uC vC uD vD r} RingCat.{max uC vC uD vD r})]
  [K.HasSheafCompose
    (forget₂ CommRingCat.{max uC vC uD vD r} RingCat.{max uC vC uD vD r})]
  [HasSheafify J AddCommGrpCat.{max uC vC uD vD r}]
  [HasSheafify K AddCommGrpCat.{max uC vC uD vD r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC uD vD r}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{max uC vC uD vD r}]
  {F : C ⥤ D} [F.IsContinuous J K]
  {S : Sheaf J CommRingCat.{max uC vC uD vD r}}
  {R : Sheaf K CommRingCat.{max uC vC uD vD r}}
  (θ : S ⟶ (F.sheafPushforwardContinuous CommRingCat.{max uC vC uD vD r} J K).obj R)
  [(pushforward.{max uC vC uD vD r} (ringHom θ)).IsRightAdjoint]

/-- The original tensor arrow obtained from the native pullback adjunction and its unit. -/
def pullbackTensorMap (M N : SheafOfModulesOfCommRing S) :
    (pullback (ringHom θ)).obj (tensorProduct S M N) ⟶
      tensorProduct R ((pullback (ringHom θ)).obj M) ((pullback (ringHom θ)).obj N) :=
  ((pullbackPushforwardAdjunction (ringHom θ)).homEquiv _ _).symm
    (tensorMap S ((pullbackPushforwardAdjunction (ringHom θ)).unit.app M)
      ((pullbackPushforwardAdjunction (ringHom θ)).unit.app N) ≫
      SheafOfModulesOfCommRing.pushforwardTensorMap θ
        ((pullback (ringHom θ)).obj M) ((pullback (ringHom θ)).obj N))

@[simp]
theorem pullbackTensorMap_adjoint (M N : SheafOfModulesOfCommRing S) :
    (pullbackPushforwardAdjunction (ringHom θ)).homEquiv _ _
      (pullbackTensorMap.{uC, vC, uD, vD, r} θ M N) =
      tensorMap S ((pullbackPushforwardAdjunction (ringHom θ)).unit.app M)
        ((pullbackPushforwardAdjunction (ringHom θ)).unit.app N) ≫
        SheafOfModulesOfCommRing.pushforwardTensorMap θ
          ((pullback (ringHom θ)).obj M) ((pullback (ringHom θ)).obj N) :=
  Equiv.apply_symm_apply _ _

/-- Currying the actual tensor-pushforward composite preserves the original global unit. -/
theorem curry_pullback_adjoint (M N : SheafOfModulesOfCommRing S)
    (P : SheafOfModulesOfCommRing R)
    (g : tensorProduct R ((pullback (ringHom θ)).obj M)
      ((pullback (ringHom θ)).obj N) ⟶ P) :
    InternalHom.curry.{uC, vC, max uD vD r} S M N ((pushforward (ringHom θ)).obj P)
      (tensorMap S ((pullbackPushforwardAdjunction (ringHom θ)).unit.app M)
        ((pullbackPushforwardAdjunction (ringHom θ)).unit.app N) ≫
        SheafOfModulesOfCommRing.pushforwardTensorMap θ
          ((pullback (ringHom θ)).obj M) ((pullback (ringHom θ)).obj N) ≫
        (pushforward (ringHom θ)).map g) =
      (pullbackPushforwardAdjunction (ringHom θ)).unit.app M ≫
        (pushforward (ringHom θ)).map
          (InternalHom.curry.{uD, vD, max uC vC r} R
            ((pullback (ringHom θ)).obj M) ((pullback (ringHom θ)).obj N) P g) ≫
        pushforwardHomMap.{uC, vC, uD, vD, max uC vC uD vD r, r} θ N P := by
  apply SheafOfModules.hom_ext
  ext U : 1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (_ : InternalHom.RawHom S N ((pushforward (ringHom θ)).obj P) U.unop) = _
  ext V n
  change g.val.app (op (F.obj V.unop.left))
    ((SheafOfModulesOfCommRing.pushforwardTensorMap θ
      ((pullback (ringHom θ)).obj M) ((pullback (ringHom θ)).obj N)).val.app
      (op V.unop.left)
      ((tensorMap S ((pullbackPushforwardAdjunction (ringHom θ)).unit.app M)
        ((pullbackPushforwardAdjunction (ringHom θ)).unit.app N)).val.app
        (op V.unop.left)
        (tensorSection S M N (op V.unop.left) (M.val.map V.unop.hom.op x) n))) =
    g.val.app (op (F.obj V.unop.left))
      (tensorSection R ((pullback (ringHom θ)).obj M) ((pullback (ringHom θ)).obj N)
        (op (F.obj V.unop.left))
        (((pullback (ringHom θ)).obj M).val.map (F.map V.unop.hom).op
          (((pullbackPushforwardAdjunction (ringHom θ)).unit.app M).val.app U x))
        (((pullbackPushforwardAdjunction (ringHom θ)).unit.app N).val.app
          (op V.unop.left) n))
  have h₁ := SheafOfModulesOfCommRing.tensor_map_tensorSection S
    ((pullbackPushforwardAdjunction (ringHom θ)).unit.app M)
    ((pullbackPushforwardAdjunction (ringHom θ)).unit.app N) (op V.unop.left)
    (M.val.map V.unop.hom.op x) n
  have h₂ := SheafOfModulesOfCommRing.pushforwardTensorMap_tensorSection θ
    ((pullback (ringHom θ)).obj M) ((pullback (ringHom θ)).obj N) (op V.unop.left)
    (((pullbackPushforwardAdjunction (ringHom θ)).unit.app M).val.app
      (op V.unop.left) (M.val.map V.unop.hom.op x))
    (((pullbackPushforwardAdjunction (ringHom θ)).unit.app N).val.app (op V.unop.left) n)
  have he := congrArg (g.val.app (op (F.obj V.unop.left)))
    ((congrArg ((SheafOfModulesOfCommRing.pushforwardTensorMap θ
      ((pullback (ringHom θ)).obj M) ((pullback (ringHom θ)).obj N)).val.app
        (op V.unop.left)) h₁).trans h₂)
  have hu := PresheafOfModules.naturality_apply
    ((pullbackPushforwardAdjunction (ringHom θ)).unit.app M).val V.unop.hom.op x
  exact he.trans (congrArg (fun z ↦ g.val.app (op (F.obj V.unop.left))
    (tensorSection R ((pullback (ringHom θ)).obj M) ((pullback (ringHom θ)).obj N)
      (op (F.obj V.unop.left)) z
      (((pullbackPushforwardAdjunction (ringHom θ)).unit.app N).val.app
        (op V.unop.left) n))) hu)

section Products

variable [HasBinaryProducts C] [HasBinaryProducts D]
  [PreservesLimitsOfShape (Discrete WalkingPair) F]
  [∀ U : C, (Over.post F).IsContinuous (J.over U) (K.over (F.obj U))]
  [∀ U : C,
    (pushforward.{max uC vC uD vD r} (restrictedRingHom (ringHom θ) U)).IsRightAdjoint]

/-- The actual tensor–Hom and module adjunctions give the tensor-pullback Hom equivalence. -/
def tensorPullbackHomEquiv (M N : SheafOfModulesOfCommRing S)
    (P : SheafOfModulesOfCommRing R) :
    (tensorProduct R ((pullback (ringHom θ)).obj M)
      ((pullback (ringHom θ)).obj N) ⟶ P) ≃
      ((pullback (ringHom θ)).obj (tensorProduct S M N) ⟶ P) :=
  (InternalHom.tensorHomEquiv.{uD, vD, max uC vC r} R
    ((pullback (ringHom θ)).obj M) ((pullback (ringHom θ)).obj N) P).trans
    (((pullbackPushforwardAdjunction (ringHom θ)).homEquiv _ _).trans
      ((Iso.homCongr (Iso.refl M)
        (pushforwardHomIso.{uC, vC, uD, vD, max uC vC uD vD r, r} θ N P)).trans
        ((InternalHom.tensorHomEquiv.{uC, vC, max uD vD r} S M N
          ((pushforward (ringHom θ)).obj P)).symm.trans
            ((pullbackPushforwardAdjunction (ringHom θ)).homEquiv _ _).symm)))

/-- The equivalence acts by precomposition with the original canonical tensor arrow. -/
theorem tensorPullbackHomEquiv_apply (M N : SheafOfModulesOfCommRing S)
    (P : SheafOfModulesOfCommRing R)
    (g : tensorProduct R ((pullback (ringHom θ)).obj M)
      ((pullback (ringHom θ)).obj N) ⟶ P) :
    tensorPullbackHomEquiv.{uC, vC, uD, vD, r} θ M N P g =
      pullbackTensorMap.{uC, vC, uD, vD, r} θ M N ≫ g := by
  apply ((pullbackPushforwardAdjunction (ringHom θ)).homEquiv _ _).injective
  simp only [tensorPullbackHomEquiv, Equiv.trans_apply, Equiv.apply_symm_apply]
  apply (InternalHom.tensorHomEquiv.{uC, vC, max uD vD r} S M N
    ((pushforward (ringHom θ)).obj P)).injective
  rw [Equiv.apply_symm_apply]
  change (pullbackPushforwardAdjunction (ringHom θ)).homEquiv _ _
      (InternalHom.curry.{uD, vD, max uC vC r} R
        ((pullback (ringHom θ)).obj M) ((pullback (ringHom θ)).obj N) P g) ≫
      pushforwardHomMap.{uC, vC, uD, vD, max uC vC uD vD r, r} θ N P =
    InternalHom.curry.{uC, vC, max uD vD r} S M N ((pushforward (ringHom θ)).obj P)
      ((pullbackPushforwardAdjunction (ringHom θ)).homEquiv _ _
        (pullbackTensorMap.{uC, vC, uD, vD, r} θ M N ≫ g))
  rw [Adjunction.homEquiv_naturality_right, pullbackTensorMap_adjoint.{uC, vC, uD, vD, r},
    Adjunction.homEquiv_unit]
  exact (curry_pullback_adjoint.{uC, vC, uD, vD, r} θ M N P g).symm

/-- The inverse is obtained from the actual Hom equivalence at the identity. -/
def pullbackTensorInverse (M N : SheafOfModulesOfCommRing S) :
    tensorProduct R ((pullback (ringHom θ)).obj M) ((pullback (ringHom θ)).obj N) ⟶
      (pullback (ringHom θ)).obj (tensorProduct S M N) :=
  (tensorPullbackHomEquiv.{uC, vC, uD, vD, r} θ M N _).symm (𝟙 _)

theorem pullbackTensorMap_inverse (M N : SheafOfModulesOfCommRing S) :
    pullbackTensorMap.{uC, vC, uD, vD, r} θ M N ≫
      pullbackTensorInverse.{uC, vC, uD, vD, r} θ M N = 𝟙 _ := by
  rw [← tensorPullbackHomEquiv_apply.{uC, vC, uD, vD, r}]
  exact (tensorPullbackHomEquiv.{uC, vC, uD, vD, r} θ M N _).apply_symm_apply (𝟙 _)

theorem pullbackTensorInverse_map (M N : SheafOfModulesOfCommRing S) :
    pullbackTensorInverse.{uC, vC, uD, vD, r} θ M N ≫
      pullbackTensorMap.{uC, vC, uD, vD, r} θ M N = 𝟙 _ := by
  apply (tensorPullbackHomEquiv.{uC, vC, uD, vD, r} θ M N _).injective
  rw [tensorPullbackHomEquiv_apply.{uC, vC, uD, vD, r},
    tensorPullbackHomEquiv_apply.{uC, vC, uD, vD, r},
    ← Category.assoc, pullbackTensorMap_inverse.{uC, vC, uD, vD, r},
    Category.id_comp, Category.comp_id]

theorem pullbackTensorMap_isIso (M N : SheafOfModulesOfCommRing S) :
    IsIso (pullbackTensorMap.{uC, vC, uD, vD, r} θ M N) :=
  ⟨⟨pullbackTensorInverse.{uC, vC, uD, vD, r} θ M N,
    pullbackTensorMap_inverse.{uC, vC, uD, vD, r} θ M N,
    pullbackTensorInverse_map.{uC, vC, uD, vD, r} θ M N⟩⟩

end Products

end SheafOfModules.Pullback.Tensor
