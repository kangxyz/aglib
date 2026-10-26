/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.Sheaf.Pullback.AdjunctionSquare
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Pullback and restriction to a ringed slice site

The direct-image comparison is the identity on section values. If the site
functor preserves binary products, the actual product comparison identifies
the right adjoints of the two composite pullbacks. The resulting left-adjoint
isomorphism satisfies the original unit and counit equations. Continuity of
the slice functor and existence of the native module left adjoints are retained
as explicit inputs; continuity alone is not an invertibility theorem.
-/

@[expose] public section

noncomputable section

universe v₁ v₂ u₁ u₂ r m

open CategoryTheory CategoryTheory.Limits Opposite

namespace SheafOfModules.Pullback

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {F : C ⥤ D} [F.IsContinuous J K]

/-- Pullback preservation supplies continuity of the actual over-site functor. -/
theorem overPost_isContinuous [HasPullbacks C]
    [PreservesLimitsOfShape WalkingCospan F] (U : C) :
    (Over.post F).IsContinuous (J.over U) (K.over (F.obj U)) := by
  let : F.PreservesOneHypercovers.{max u₁ v₁} J K :=
    Functor.PreservesOneHypercovers.of_coverPreserving
      (CoverPreserving.of_isContinuous F J K)
  infer_instance

variable
  {S : Sheaf J RingCat.{r}} {R : Sheaf K RingCat.{r}}
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{r} J K).obj R)
  (U : C) [(Over.post F).IsContinuous (J.over U) (K.over (F.obj U))]

/-- The structural ring map on the actual slice site, induced by the forgetful square. -/
def restrictedRingHom :
    S.over U ⟶ ((Over.post F).sheafPushforwardContinuous RingCat.{r}
      (J.over U) (K.over (F.obj U))).obj (R.over (F.obj U)) :=
  ⟨Functor.whiskerLeft (Over.forget U).op φ.hom⟩

@[simp]
theorem restrictedRingHom_app (V : (Over U)ᵒᵖ) :
    (restrictedRingHom φ U).hom.app V = φ.hom.app (op V.unop.left) := rfl

/-- Restricting direct image agrees with direct image on the actual over-site. -/
def restrictionPushforwardIso :
    pushforward.{m} φ ⋙ overFunctor S U ≅
      overFunctor R (F.obj U) ⋙ pushforward.{m} (restrictedRingHom φ U) :=
  Iso.refl _

@[simp]
theorem restrictionPushforwardIso_hom_app_apply (N : SheafOfModules.{m} R)
    (V : (Over U)ᵒᵖ) (x : ((pushforward φ).obj N).val.obj (op V.unop.left)) :
    (ModuleCat.Hom.hom
      (A := ((overFunctor S U).obj ((pushforward φ).obj N)).val.obj V)
      (B := ((pushforward (restrictedRingHom φ U)).obj
        ((overFunctor R (F.obj U)).obj N)).val.obj V)
      (((restrictionPushforwardIso φ U).hom.app N).val.app V)) x = x := rfl

@[simp]
theorem restrictionPushforwardIso_inv_app_apply (N : SheafOfModules.{m} R)
    (V : (Over U)ᵒᵖ) (x : ((pushforward φ).obj N).val.obj (op V.unop.left)) :
    (ModuleCat.Hom.hom
      (A := ((pushforward (restrictedRingHom φ U)).obj
        ((overFunctor R (F.obj U)).obj N)).val.obj V)
      (B := ((overFunctor S U).obj ((pushforward φ).obj N)).val.obj V)
      (((restrictionPushforwardIso φ U).inv.app N).val.app V)) x = x := rfl

section Products

variable [HasBinaryProducts C] [HasBinaryProducts D]
  [PreservesLimitsOfShape (Discrete WalkingPair) F]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual product comparison, regarded as an isomorphism of over-site functors. -/
def overStarPostIso :
    Over.star U ⋙ Over.post F ≅ F ⋙ Over.star (F.obj U) :=
  NatIso.ofComponents
    (fun V ↦ Over.isoMk (PreservesLimitPair.iso F U V) (by
      change (PreservesLimitPair.iso F U V).hom ≫
        ((Over.star (F.obj U)).obj (F.obj V)).hom = F.map ((Over.star U).obj V).hom
      simp only [PreservesLimitPair.iso_hom, Over.star_obj_hom, prod.lift_fst,
        prodComparison_fst]))
    (fun {V W} f ↦ by
      apply Over.OverMorphism.ext
      change F.map (prod.map (𝟙 U) f) ≫ prodComparison F U W =
        prodComparison F U V ≫ prod.map (𝟙 (F.obj U)) (F.map f)
      exact (prodComparison_natural F (𝟙 U) f).trans
        (congrArg (fun k : F.obj U ⟶ F.obj U ↦
          prodComparison F U V ≫ prod.map k (F.map f)) (F.map_id U)))

@[simp]
theorem overStarPostIso_hom_app_left (V : C) :
    ((overStarPostIso (F := F) U).hom.app V).left = prodComparison F U V := rfl

local instance : (F ⋙ Over.star (F.obj U)).IsContinuous J (K.over (F.obj U)) :=
  Functor.isContinuous_comp _ _ J K _

local instance : (Over.star U ⋙ Over.post F).IsContinuous J (K.over (F.obj U)) :=
  Functor.isContinuous_comp _ _ J (J.over U) _

/-- Naturality of the structural ring map supplies the product-square coefficient equation. -/
theorem restrictionRightAdjoint_ring_square :
    (φ ≫ (F.sheafPushforwardContinuous RingCat.{r} J K).map
      (pushforwardOver (R := R) (F.obj U))) ≫
      (Functor.sheafPushforwardContinuousNatTrans
        (overStarPostIso (F := F) U).hom RingCat.{r} J (K.over (F.obj U))).app
          (R.over (F.obj U)) =
    pushforwardOver (R := S) U ≫
      ((Over.star U).sheafPushforwardContinuous RingCat.{r} J (J.over U)).map
        (restrictedRingHom φ U) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext V
  let a : S.obj.obj V ⟶ R.obj.obj (op (F.obj V.unop)) := φ.hom.app V
  let b : S.obj.obj (op (U ⨯ V.unop)) ⟶ R.obj.obj (op (F.obj (U ⨯ V.unop))) :=
    φ.hom.app (op (U ⨯ V.unop))
  change (a ≫ R.obj.map prod.snd.op) ≫
    R.obj.map (prodComparison F U V.unop).op =
      S.obj.map prod.snd.op ≫ b
  have h : R.obj.map (prod.snd : F.obj U ⨯ F.obj V.unop ⟶ F.obj V.unop).op ≫
      R.obj.map (prodComparison F U V.unop).op =
      R.obj.map (F.map (prod.snd : U ⨯ V.unop ⟶ V.unop)).op :=
    (R.obj.map_comp _ _).symm.trans
      (congrArg (fun k : F.obj (U ⨯ V.unop) ⟶ F.obj V.unop ↦ R.obj.map k.op)
        (prodComparison_snd F U V.unop))
  exact (Category.assoc a _ _).trans
    ((congrArg (fun k : R.obj.obj (op (F.obj V.unop)) ⟶
      R.obj.obj (op (F.obj (U ⨯ V.unop))) ↦ a ≫ k) h).trans
      (φ.hom.naturality (prod.snd : U ⨯ V.unop ⟶ V.unop).op).symm)

/-- The right-adjoint square supplied by preservation of actual binary products. -/
def restrictionRightAdjointIso :
    pushforward.{m} (pushforwardOver (R := R) (F.obj U)) ⋙ pushforward φ ≅
      pushforward (restrictedRingHom φ U) ⋙
        pushforward (pushforwardOver (R := S) U) :=
  pushforwardComp φ (pushforwardOver (R := R) (F.obj U)) ≪≫
    pushforwardCongr₂ _ (overStarPostIso (F := F) U)
      (restrictionRightAdjoint_ring_square φ U) ≪≫
    (pushforwardComp (pushforwardOver (R := S) U) (restrictedRingHom φ U)).symm

theorem restrictionRightAdjointIso_hom_app_apply
    (N : SheafOfModules.{m} (R.over (F.obj U))) (V : Cᵒᵖ)
    (x : ((pushforward (pushforwardOver (R := R) (F.obj U)) ⋙
      pushforward φ).obj N).val.obj V) :
    ((restrictionRightAdjointIso φ U).hom.app N).val.app V x =
      N.val.map ((overStarPostIso (F := F) U).hom.app V.unop).op x := rfl

/-- Section formula for the native unit of over-restriction. -/
theorem overRestrictionUnit_apply (M : SheafOfModules.{m} S) (V : Cᵒᵖ)
    (x : M.val.obj V) :
    ((overPushforwardOverAdj (R := S) U).unit.app M).val.app V x =
      M.val.map prod.snd.op x := by
  change M.val.map ((Over.forgetAdjStar U).counit.app V.unop).op x = _
  rw [Over.forgetAdjStar_counit_app]
  rfl

/-- Section formula for the native counit of over-restriction. -/
theorem overRestrictionCounit_apply (M : SheafOfModules.{m} (S.over U))
    (V : (Over U)ᵒᵖ)
    (x : ((overFunctor S U).obj
      ((pushforward (pushforwardOver (R := S) U)).obj M)).val.obj V) :
    ((overPushforwardOverAdj (R := S) U).counit.app M).val.app V x =
      M.val.map ((Over.forgetAdjStar U).unit.app V.unop).op x := rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The partial mate of the product square is the identity on section values. -/
theorem restrictionRightAdjointIso_mate_apply (N : SheafOfModules.{m} R)
    (V : (Over U)ᵒᵖ) (x : N.val.obj (op (F.obj V.unop.left))) :
    (Adjunction.squareRestrictionMap (overPushforwardOverAdj (R := S) U)
      (overPushforwardOverAdj (R := R) (F.obj U))
      (restrictionRightAdjointIso φ U) N).val.app V x = x := by
  rw [Adjunction.squareRestrictionMap, Adjunction.homEquiv_counit]
  change (N.val.presheaf.map
      ((Over.forgetAdjStar (F.obj U)).counit.app (F.obj V.unop.left)).op ≫
    N.val.presheaf.map (prodComparison F U V.unop.left).op ≫
    N.val.presheaf.map (F.map ((Over.forgetAdjStar U).unit.app V.unop).left).op) x = x
  rw [Over.forgetAdjStar_counit_app]
  rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp]
  have h : F.map ((Over.forgetAdjStar U).unit.app V.unop).left ≫
      prodComparison F U V.unop.left ≫ prod.snd = 𝟙 _ := by
    simp [Over.forgetAdjStar_unit_app_left, ← F.map_comp]
  simp only [Category.assoc, h, op_id]
  change (N.val.presheaf.map (𝟙 (op (F.obj V.unop.left)))) x = x
  exact congrArg (fun k : N.val.presheaf.obj (op (F.obj V.unop.left)) ⟶
    N.val.presheaf.obj (op (F.obj V.unop.left)) ↦ k x)
      (N.val.presheaf.map_id (op (F.obj V.unop.left)))

/-- The actual product-square mate equals the direct-image restriction comparison. -/
theorem restrictionRightAdjointIso_mate (N : SheafOfModules.{m} R) :
    Adjunction.squareRestrictionMap (overPushforwardOverAdj (R := S) U)
      (overPushforwardOverAdj (R := R) (F.obj U))
      (restrictionRightAdjointIso φ U) N =
    (restrictionPushforwardIso φ U).hom.app N := by
  ext V x
  exact restrictionRightAdjointIso_mate_apply φ U N V x

variable [(pushforward.{m} φ).IsRightAdjoint]
  [(pushforward.{m} (restrictedRingHom φ U)).IsRightAdjoint]

/-- Pullback commutes with restriction to the actual ringed slice, with its native left adjoints. -/
def restrictionPullbackIso :
    pullback.{m} φ ⋙ overFunctor R (F.obj U) ≅
      overFunctor S U ⋙ pullback.{m} (restrictedRingHom φ U) :=
  Adjunction.squareLeftIso (pullbackPushforwardAdjunction φ)
    (pullbackPushforwardAdjunction (restrictedRingHom φ U))
    (overPushforwardOverAdj (R := S) U)
    (overPushforwardOverAdj (R := R) (F.obj U))
    (restrictionRightAdjointIso φ U)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The slice comparison preserves adjoining an arrow by the original module adjunction. -/
theorem restrictionAdjoint_eq {M : SheafOfModules.{m} S} {N : SheafOfModules.{m} R}
    (f : M ⟶ (pushforward φ).obj N) :
    (overFunctor R (F.obj U)).map
        (((pullbackPushforwardAdjunction φ).homEquiv M N).symm f) =
      (restrictionPullbackIso φ U).hom.app M ≫
        ((pullbackPushforwardAdjunction (restrictedRingHom φ U)).homEquiv _ _).symm
          ((overFunctor S U).map f ≫ (restrictionPushforwardIso φ U).hom.app N) := by
  simpa only [restrictionPullbackIso, restrictionRightAdjointIso_mate,
    overFunctor] using
    Adjunction.squareAdjoint_eq (pullbackPushforwardAdjunction φ)
      (pullbackPushforwardAdjunction (restrictedRingHom φ U))
      (overPushforwardOverAdj (R := S) U)
      (overPushforwardOverAdj (R := R) (F.obj U))
      (restrictionRightAdjointIso φ U) f

/-- The original-unit equation, in the orientation used by internal-Hom pullback. -/
theorem restrictionUnit (M : SheafOfModules.{m} S) :
    (pullbackPushforwardAdjunction (restrictedRingHom φ U)).unit.app (M.over U) ≫
      (pushforward (restrictedRingHom φ U)).map ((restrictionPullbackIso φ U).inv.app M) =
    (overFunctor S U).map ((pullbackPushforwardAdjunction φ).unit.app M) ≫
      (restrictionPushforwardIso φ U).hom.app ((pullback φ).obj M) := by
  simpa only [restrictionPullbackIso, restrictionRightAdjointIso_mate,
    over, overFunctor] using
    Adjunction.squareUnit (pullbackPushforwardAdjunction φ)
      (pullbackPushforwardAdjunction (restrictedRingHom φ U))
      (overPushforwardOverAdj (R := S) U)
      (overPushforwardOverAdj (R := R) (F.obj U))
      (restrictionRightAdjointIso φ U) M

/-- The counit equation for the same native comparison and actual direct-image map. -/
theorem restrictionCounit (N : SheafOfModules.{m} R) :
    (pullback (restrictedRingHom φ U)).map ((restrictionPushforwardIso φ U).hom.app N) ≫
      (pullbackPushforwardAdjunction (restrictedRingHom φ U)).counit.app
        (N.over (F.obj U)) =
    (restrictionPullbackIso φ U).inv.app ((pushforward φ).obj N) ≫
      (overFunctor R (F.obj U)).map ((pullbackPushforwardAdjunction φ).counit.app N) := by
  simpa only [restrictionPullbackIso, restrictionRightAdjointIso_mate,
    over, overFunctor] using
    Adjunction.squareCounit (pullbackPushforwardAdjunction φ)
      (pullbackPushforwardAdjunction (restrictedRingHom φ U))
      (overPushforwardOverAdj (R := S) U)
      (overPushforwardOverAdj (R := R) (F.obj U))
      (restrictionRightAdjointIso φ U) N

/-- The native slice adjunction as a bijection between restricted module morphisms. -/
def restrictionHomEquiv (M : SheafOfModules.{m} S) (N : SheafOfModules.{m} R) :
    (((pullback φ).obj M).over (F.obj U) ⟶ N.over (F.obj U)) ≃
      (M.over U ⟶ ((pushforward φ).obj N).over U) :=
  (Iso.homCongr ((restrictionPullbackIso φ U).app M) (Iso.refl _)).trans
    (((pullbackPushforwardAdjunction (restrictedRingHom φ U)).homEquiv _ _).trans
      (Iso.homCongr (Iso.refl _) ((restrictionPushforwardIso φ U).app N).symm))

theorem restrictionHomEquiv_eq (M : SheafOfModules.{m} S) (N : SheafOfModules.{m} R)
    (h : ((pullback φ).obj M).over (F.obj U) ⟶ N.over (F.obj U)) :
    restrictionHomEquiv φ U M N h =
      (overFunctor S U).map ((pullbackPushforwardAdjunction φ).unit.app M) ≫
        (restrictionPushforwardIso φ U).hom.app ((pullback φ).obj M) ≫
        (pushforward (restrictedRingHom φ U)).map h ≫
        (restrictionPushforwardIso φ U).inv.app N := by
  simp only [restrictionHomEquiv, Equiv.trans_apply, Iso.homCongr_apply,
    Iso.refl_inv, Iso.refl_hom, Iso.symm_hom, Category.id_comp, Category.comp_id]
  change (pullbackPushforwardAdjunction (restrictedRingHom φ U)).homEquiv _ _
      ((restrictionPullbackIso φ U).inv.app M ≫ h) ≫
        (restrictionPushforwardIso φ U).inv.app N = _
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, restrictionUnit]
  simp only [Category.assoc]

/-- The equivalence uses the original global unit followed by the supplied section arrow. -/
theorem restrictionHomEquiv_apply (M : SheafOfModules.{m} S) (N : SheafOfModules.{m} R)
    (h : ((pullback φ).obj M).over (F.obj U) ⟶ N.over (F.obj U))
    (V : (Over U)ᵒᵖ) (x : M.val.obj (op V.unop.left)) :
    (restrictionHomEquiv φ U M N h).val.app V x =
      h.val.app ((Over.post F).op.obj V)
        (((pullbackPushforwardAdjunction φ).unit.app M).val.app
          (op V.unop.left) x) := by
  rw [restrictionHomEquiv_eq]
  rfl

end Products

end SheafOfModules.Pullback
