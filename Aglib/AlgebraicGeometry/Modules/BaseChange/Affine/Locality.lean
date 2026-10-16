/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.Square

/-!
# Open-local comparison of the actual square mate

The original restriction/whiskering equations identify the actual mate on
source and target opens. Canonical pullback, pushforward and adjunction-unit
maps are retained, with no flatness premise on the base change.

Source: `R5Lab/AlgebraicGeometry/Curves/Degree/AffineModuleBaseChange.lean`, frozen R5 integration
`79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`0739a4c1e7297a8f1dec99f8f53914339710e9240fa56c70a90ae2127581ed06`. Selected original ranges:
[[1022, 1509]].
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry Opposite Module TopologicalSpace
open TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules.BaseChange.Affine.Square
universe u
variable {P X Y T : Scheme.{u}}
section AdjunctionTransport
variable {C D : Type*} [Category C] [Category D]
  {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C}


end AdjunctionTransport

theorem conjugateEquiv_restrictFunctorIsoPullback_hom (f : X ⟶ Y) [IsOpenImmersion f] :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.restrictAdjunction f)
      (Scheme.Modules.restrictFunctorIsoPullback f).hom = 𝟙 _ := by
  change (conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.restrictAdjunction f))
    ((conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.restrictAdjunction f)).symm (𝟙 _)) = 𝟙 _
  exact Equiv.apply_symm_apply _ _

theorem conjugateEquiv_restrictFunctorIsoPullback_inv (f : X ⟶ Y) [IsOpenImmersion f] :
    conjugateEquiv (Scheme.Modules.restrictAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.restrictFunctorIsoPullback f).inv = 𝟙 _ := by
  change (conjugateEquiv (Scheme.Modules.restrictAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f))
    ((conjugateEquiv (Scheme.Modules.restrictAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction f)).symm (𝟙 _)) = 𝟙 _
  exact Equiv.apply_symm_apply _ _

/-- The canonical pullback-square comparison after restriction to the displayed open. -/
def nativeRestrictionSquareIso (f : X ⟶ Y) (U : Y.Opens) :
    Scheme.Modules.restrictFunctor U.ι ⋙ Scheme.Modules.pullback (f ∣_ U) ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι :=
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback U.ι) _ ≪≫
    pullbackSquareIso (f ⁻¹ᵁ U).ι (f ∣_ U) f U.ι (morphismRestrict_ι f U).symm ≪≫
      Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).symm

theorem nativeRestrictionSquareIso_eq (f : X ⟶ Y) (U : Y.Opens) :
    nativeRestrictionSquareIso f U = (Scheme.Modules.Pullback.OpenRestriction.localPullbackIso f
      U).symm := by
  apply Iso.ext
  apply (conjugateEquiv (Scheme.Modules.Pullback.OpenRestriction.restrictedLeftAdjunction f U)
    ((Scheme.Modules.restrictAdjunction U.ι).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)))).injective
  simp only [Scheme.Modules.Pullback.OpenRestriction.localPullbackIso, Iso.symm_hom,
    Scheme.Modules.Pullback.OpenRestriction.restrictedRightAdjunction]
  rw [conjugateEquiv_leftAdjointUniq_ofNatIsoRight_inv]
  change conjugateEquiv ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
    (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι))
    ((Scheme.Modules.restrictAdjunction U.ι).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))) _ = _
  unfold nativeRestrictionSquareIso
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_hom]
  rw [← Category.assoc]
  rw [← conjugateEquiv_comp _
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (f ⁻¹ᵁ U).ι)) _]
  rw [← conjugateEquiv_comp _
    ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))) _]
  rw [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    conjugateEquiv_restrictFunctorIsoPullback_inv, conjugateEquiv_restrictFunctorIsoPullback_hom,
    conjugateEquiv_pullbackSquareIso]
  ext M U x
  simp only [Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.id_app,
    NatTrans.comp_app, CategoryTheory.Functor.map_id, Scheme.Modules.Hom.comp_app,
    ]
  rfl



theorem restrictFunctorIsoPullback_unit (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) :
    (Scheme.Modules.restrictAdjunction f).unit.app M ≫
      (Scheme.Modules.pushforward f).map ((Scheme.Modules.restrictFunctorIsoPullback f).hom.app M) =
        (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ M

theorem restrictFunctorIsoPullback_unit_inv (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
      (Scheme.Modules.pushforward f).map ((Scheme.Modules.restrictFunctorIsoPullback f).inv.app M) =
        (Scheme.Modules.restrictAdjunction f).unit.app M := by
  rw [← restrictFunctorIsoPullback_unit f M, Category.assoc, ← Functor.map_comp,
    Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]
  erw [Category.comp_id]

end AlgebraicGeometry.Scheme.Modules.BaseChange.Affine.Square


namespace AlgebraicGeometry.Scheme.Modules.BaseChange.Affine.Square
universe u
variable {P X Y T : Scheme.{u}}

/-- The canonical comparison identifying the composite morphism over the test open. -/
def testOpenCompositeIso (f : X ⟶ Y) (U : X.Opens) :
    Scheme.Modules.pullback f ⋙ Scheme.Modules.restrictFunctor U.ι ≅
      Scheme.Modules.pullback (U.ι ≫ f) :=
  Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorIsoPullback U.ι) ≪≫
    Scheme.Modules.pullbackComp U.ι f

theorem conjugateEquiv_testOpenCompositeIso_hom (f : X ⟶ Y) (U : X.Opens) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction (U.ι ≫ f))
      ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
        (Scheme.Modules.restrictAdjunction U.ι))
      (testOpenCompositeIso f U).hom = (Scheme.Modules.pushforwardComp U.ι f).inv := by
  unfold testOpenCompositeIso
  simp only [Iso.trans_hom, Functor.isoWhiskerLeft_hom]
  rw [← conjugateEquiv_comp _
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction U.ι)) _]
  rw [conjugateEquiv_whiskerLeft, conjugateEquiv_restrictFunctorIsoPullback_hom,
    conjugateEquiv_pullbackComp_hom]
  ext M U x
  simp only [Functor.whiskerRight_app, NatTrans.id_app, NatTrans.comp_app,
    Scheme.Modules.Hom.comp_app]
  rfl


theorem conjugateEquiv_testOpenCompositeIso_inv (f : X ⟶ Y) (U : X.Opens) :
    conjugateEquiv
      ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
        (Scheme.Modules.restrictAdjunction U.ι))
      (Scheme.Modules.pullbackPushforwardAdjunction (U.ι ≫ f))
      (testOpenCompositeIso f U).inv = (Scheme.Modules.pushforwardComp U.ι f).hom := by
  apply (cancel_mono (Scheme.Modules.pushforwardComp U.ι f).inv).mp
  rw [← conjugateEquiv_testOpenCompositeIso_hom]
  rw [conjugateEquiv_comm _ _ (Iso.hom_inv_id (testOpenCompositeIso f U)),
    conjugateEquiv_testOpenCompositeIso_hom]
  exact (Iso.hom_inv_id _).symm

/-- The commutativity equality for the actual square over the test open. -/
theorem testOpenCondition (a : P ⟶ X) (b : P ⟶ T) (f : X ⟶ Y) (g : T ⟶ Y)
    (h : a ≫ f = b ≫ g) (U : T.Opens) :
    ((b ⁻¹ᵁ U).ι ≫ a) ≫ f = (b ∣_ U) ≫ (U.ι ≫ g) := by
  rw [Category.assoc, h, ← Category.assoc, ← morphismRestrict_ι, Category.assoc]

/-- The actual pasted commutative square over the displayed test open. -/
def testOpenPastedSquare (a : P ⟶ X) (b : P ⟶ T) (f : X ⟶ Y) (g : T ⟶ Y)
    (h : a ≫ f = b ≫ g) (U : T.Opens) :
    Scheme.Modules.pullback (U.ι ≫ g) ⋙ Scheme.Modules.pullback (b ∣_ U) ⟶
      Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback ((b ⁻¹ᵁ U).ι ≫ a) :=
  Functor.whiskerRight (testOpenCompositeIso g U).inv _ ≫
    (TwoSquare.hComp (pullbackSquareIso a b f g h).hom
      (Scheme.Modules.Pullback.OpenRestriction.localPullbackIso b U).inv).natTrans ≫
    Functor.whiskerLeft _ (testOpenCompositeIso a (b ⁻¹ᵁ U)).hom

theorem conjugateEquiv_nativeRestrictionSquareIso (f : X ⟶ Y) (U : Y.Opens) :
    conjugateEquiv
      ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
        (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι))
      ((Scheme.Modules.restrictAdjunction U.ι).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)))
      (nativeRestrictionSquareIso f U).hom =
        (Scheme.Modules.Pullback.OpenRestriction.pushforwardSquare f U).hom := by
  rw [nativeRestrictionSquareIso_eq]
  simp only [Scheme.Modules.Pullback.OpenRestriction.localPullbackIso, Iso.symm_hom,
    Scheme.Modules.Pullback.OpenRestriction.restrictedRightAdjunction]
  exact conjugateEquiv_leftAdjointUniq_ofNatIsoRight_inv _ _ _

theorem testOpenPastedSquare_eq (a : P ⟶ X) (b : P ⟶ T) (f : X ⟶ Y) (g : T ⟶ Y)
    (h : a ≫ f = b ≫ g) (U : T.Opens) :
    testOpenPastedSquare a b f g h U =
      (pullbackSquareIso ((b ⁻¹ᵁ U).ι ≫ a) (b ∣_ U) f (U.ι ≫ g)
        (testOpenCondition a b f g h U)).hom := by
  apply (conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction ((b ⁻¹ᵁ U).ι ≫ a)))
    ((Scheme.Modules.pullbackPushforwardAdjunction (U.ι ≫ g)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (b ∣_ U)))).injective
  rw [conjugateEquiv_pullbackSquareIso]
  unfold testOpenPastedSquare
  rw [← Category.assoc]
  rw [← conjugateEquiv_comp _
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      ((Scheme.Modules.pullbackPushforwardAdjunction a).comp
        (Scheme.Modules.restrictAdjunction (b ⁻¹ᵁ U).ι))) _]
  rw [← conjugateEquiv_comp _
    (((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.restrictAdjunction U.ι)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (b ∣_ U))) _]
  rw [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    conjugateEquiv_testOpenCompositeIso_hom, conjugateEquiv_testOpenCompositeIso_inv]
  have hs := congrArg Iso.hom (nativeRestrictionSquareIso_eq b U)
  simp only [Iso.symm_hom] at hs
  erw [← hs]
  unfold TwoSquare.hComp
  dsimp only [TwoSquare.mk, TwoSquare.natTrans]
  simp only [← Category.assoc]
  rw [← conjugateEquiv_comp _
    (((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction a)).comp
        (Scheme.Modules.restrictAdjunction (b ⁻¹ᵁ U).ι)) _]
  rw [← conjugateEquiv_comp _
    (((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction b)).comp
        (Scheme.Modules.restrictAdjunction (b ⁻¹ᵁ U).ι)) _]
  rw [← conjugateEquiv_comp _
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      ((Scheme.Modules.pullbackPushforwardAdjunction b).comp
        (Scheme.Modules.restrictAdjunction (b ⁻¹ᵁ U).ι))) _]
  rw [← conjugateEquiv_comp _
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      ((Scheme.Modules.restrictAdjunction U.ι).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (b ∣_ U)))) _]
  rw [conjugateEquiv_associator_hom, conjugateEquiv_whiskerRight,
    conjugateEquiv_pullbackSquareIso, conjugateEquiv_associator_inv,
    conjugateEquiv_whiskerLeft, conjugateEquiv_associator_hom]
  rw [conjugateEquiv_nativeRestrictionSquareIso]
  ext M V
  simp only [Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app, Category.id_comp, Category.comp_id]
  unfold pushforwardSquareIso Scheme.Modules.Pullback.OpenRestriction.pushforwardSquare
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app, Category.id_comp, Category.comp_id,
    Scheme.Modules.pushforward_obj_presheaf_map]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]
  rw [← Functor.map_comp]
  congr 1

-- The canonical composite-functor term requires deeper bounded reduction.
set_option maxRecDepth 4096 in
theorem testOpenPastedSquare_whisker (a : P ⟶ X) (b : P ⟶ T)
    (f : X ⟶ Y) (g : T ⟶ Y) (h : a ≫ f = b ≫ g) (U : T.Opens) :
    testOpenPastedSquare a b f g h U =
      (((TwoSquare.hComp (pullbackSquareIso a b f g h).hom
        (Scheme.Modules.Pullback.OpenRestriction.localPullbackIso b U).inv).whiskerTop
          (testOpenCompositeIso g U).inv).whiskerBottom
            (testOpenCompositeIso a (b ⁻¹ᵁ U)).hom).natTrans := rfl

-- This mate normalization elaborates several dependent scheme-module compositions.
theorem moduleSquareBaseChangeMap_testOpen (a : P ⟶ X) (b : P ⟶ T)
    (f : X ⟶ Y) (g : T ⟶ Y) (h : a ≫ f = b ≫ g) (U : T.Opens) (M : X.Modules) :
    moduleSquareBaseChangeMap ((b ⁻¹ᵁ U).ι ≫ a) (b ∣_ U) f (U.ι ≫ g)
        (testOpenCondition a b f g h U) M =
      (testOpenCompositeIso g U).inv.app ((Scheme.Modules.pushforward f).obj M) ≫
        (Scheme.Modules.restrictFunctor U.ι).map (moduleSquareBaseChangeMap a b f g h M) ≫
          Scheme.Modules.Pullback.OpenRestriction.restrictedPushforwardMap b U
            ((Scheme.Modules.pullback a).obj M) ≫
            (Scheme.Modules.pushforward (b ∣_ U)).map
              ((testOpenCompositeIso a (b ⁻¹ᵁ U)).hom.app M) := by
  rw [← baseChangeNatTransOfSquare_app ((b ⁻¹ᵁ U).ι ≫ a) (b ∣_ U) f (U.ι ≫ g)
    (testOpenCondition a b f g h U) M]
  unfold baseChangeNatTransOfSquare
  rw [← testOpenPastedSquare_eq a b f g h U]
  rw [testOpenPastedSquare_whisker a b f g h U]
  rw [mateEquiv_whiskerBottom, mateEquiv_whiskerTop]
  simp only [TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app,
    Functor.comp_obj, Category.assoc]
  rw [testOpenPastedMate a b f g h U M]
  simp only [Category.assoc]

end AlgebraicGeometry.Scheme.Modules.BaseChange.Affine.Square


namespace AlgebraicGeometry.Scheme.Modules.BaseChange.Affine.Square
universe u
variable {P X Y T : Scheme.{u}}

/-- The canonical comparison for the first projection after open base change. -/
def openFirstCompositeIso {Z : Scheme.{u}} (i : X ⟶ Y) [IsOpenImmersion i] (a : Z ⟶ X) :
    Scheme.Modules.restrictFunctor i ⋙ Scheme.Modules.pullback a ≅
      Scheme.Modules.pullback (a ≫ i) :=
  Functor.isoWhiskerRight (Scheme.Modules.restrictFunctorIsoPullback i) _ ≪≫
    Scheme.Modules.pullbackComp a i

theorem conjugateEquiv_openFirstCompositeIso_hom {Z : Scheme.{u}}
    (i : X ⟶ Y) [IsOpenImmersion i] (a : Z ⟶ X) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction (a ≫ i))
      ((Scheme.Modules.restrictAdjunction i).comp
        (Scheme.Modules.pullbackPushforwardAdjunction a))
      (openFirstCompositeIso i a).hom = (Scheme.Modules.pushforwardComp a i).inv := by
  unfold openFirstCompositeIso
  simp only [Iso.trans_hom, Functor.isoWhiskerRight_hom]
  rw [← conjugateEquiv_comp _
    ((Scheme.Modules.pullbackPushforwardAdjunction i).comp
      (Scheme.Modules.pullbackPushforwardAdjunction a)) _]
  rw [conjugateEquiv_whiskerRight, conjugateEquiv_restrictFunctorIsoPullback_hom,
    conjugateEquiv_pullbackComp_hom]
  ext M U x
  simp only [Functor.whiskerLeft_app, NatTrans.id_app, NatTrans.comp_app,
    Scheme.Modules.Hom.comp_app]
  rfl

theorem conjugateEquiv_openFirstCompositeIso_inv {Z : Scheme.{u}}
    (i : X ⟶ Y) [IsOpenImmersion i] (a : Z ⟶ X) :
    conjugateEquiv
      ((Scheme.Modules.restrictAdjunction i).comp
        (Scheme.Modules.pullbackPushforwardAdjunction a))
      (Scheme.Modules.pullbackPushforwardAdjunction (a ≫ i))
      (openFirstCompositeIso i a).inv = (Scheme.Modules.pushforwardComp a i).hom := by
  apply (cancel_mono (Scheme.Modules.pushforwardComp a i).inv).mp
  rw [← conjugateEquiv_openFirstCompositeIso_hom]
  rw [conjugateEquiv_comm _ _ (Iso.hom_inv_id (openFirstCompositeIso i a)),
    conjugateEquiv_openFirstCompositeIso_hom]
  exact (Iso.hom_inv_id _).symm

variable (f : X ⟶ Y) (U : Y.Opens)
variable (a : P ⟶ (f ⁻¹ᵁ U).toScheme) (b : P ⟶ T) (g : T ⟶ U.toScheme)
variable (h : a ≫ (f ∣_ U) = b ≫ g)

include h
theorem baseOpenCondition : (a ≫ (f ⁻¹ᵁ U).ι) ≫ f = b ≫ (g ≫ U.ι) := by
  rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc, h, Category.assoc]

/-- The pasted commutative square obtained from the displayed base open. -/
def baseOpenPastedSquare :
    Scheme.Modules.pullback (g ≫ U.ι) ⋙ Scheme.Modules.pullback b ⟶
      Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback (a ≫ (f ⁻¹ᵁ U).ι) :=
  Functor.whiskerRight (openFirstCompositeIso U.ι g).inv _ ≫
    (TwoSquare.hComp (Scheme.Modules.Pullback.OpenRestriction.localPullbackIso f U).inv
      (pullbackSquareIso a b (f ∣_ U) g h).hom).natTrans ≫
    Functor.whiskerLeft _ (openFirstCompositeIso (f ⁻¹ᵁ U).ι a).hom

theorem baseOpenPastedSquare_eq :
    baseOpenPastedSquare f U a b g h =
      (pullbackSquareIso (a ≫ (f ⁻¹ᵁ U).ι) b f (g ≫ U.ι)
        (baseOpenCondition f U a b g h)).hom := by
  apply (conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (a ≫ (f ⁻¹ᵁ U).ι)))
    ((Scheme.Modules.pullbackPushforwardAdjunction (g ≫ U.ι)).comp
      (Scheme.Modules.pullbackPushforwardAdjunction b))).injective
  rw [conjugateEquiv_pullbackSquareIso]
  unfold baseOpenPastedSquare
  rw [← Category.assoc]
  rw [← conjugateEquiv_comp _
    ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      ((Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι).comp
        (Scheme.Modules.pullbackPushforwardAdjunction a))) _]
  rw [← conjugateEquiv_comp _
    (((Scheme.Modules.restrictAdjunction U.ι).comp
      (Scheme.Modules.pullbackPushforwardAdjunction g)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction b)) _]
  rw [conjugateEquiv_whiskerLeft, conjugateEquiv_whiskerRight,
    conjugateEquiv_openFirstCompositeIso_hom, conjugateEquiv_openFirstCompositeIso_inv]
  have hs := congrArg Iso.hom (nativeRestrictionSquareIso_eq f U)
  simp only [Iso.symm_hom] at hs
  erw [← hs]
  unfold TwoSquare.hComp
  dsimp only [TwoSquare.mk, TwoSquare.natTrans]
  simp only [← Category.assoc]
  rw [← conjugateEquiv_comp _
    (((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (Scheme.Modules.restrictAdjunction (f ⁻¹ᵁ U).ι)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction a)) _]
  rw [← conjugateEquiv_comp _
    (((Scheme.Modules.restrictAdjunction U.ι).comp
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))).comp
        (Scheme.Modules.pullbackPushforwardAdjunction a)) _]
  rw [← conjugateEquiv_comp _
    ((Scheme.Modules.restrictAdjunction U.ι).comp
      ((Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction a))) _]
  rw [← conjugateEquiv_comp _
    ((Scheme.Modules.restrictAdjunction U.ι).comp
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction b))) _]
  rw [conjugateEquiv_associator_hom, conjugateEquiv_whiskerRight,
    conjugateEquiv_nativeRestrictionSquareIso, conjugateEquiv_associator_inv,
    conjugateEquiv_whiskerLeft, conjugateEquiv_pullbackSquareIso,
    conjugateEquiv_associator_hom]
  ext M V
  simp only [Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforward_map_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app, Category.id_comp, Category.comp_id]
  unfold pushforwardSquareIso Scheme.Modules.Pullback.OpenRestriction.pushforwardSquare
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.pushforwardComp_hom_app_app, Scheme.Modules.pushforwardComp_inv_app_app,
    Scheme.Modules.pushforwardCongr_hom_app_app, Category.id_comp, Category.comp_id,
    Scheme.Modules.pushforward_obj_presheaf_map]
  erw [Category.id_comp, Category.id_comp, Category.comp_id]
  rw [← Functor.map_comp]
  congr 1

-- The canonical functor composites require a bounded deeper reduction.
theorem baseOpenPastedSquare_whisker :
    baseOpenPastedSquare f U a b g h =
      (((TwoSquare.hComp (Scheme.Modules.Pullback.OpenRestriction.localPullbackIso f U).inv
        (pullbackSquareIso a b (f ∣_ U) g h).hom).whiskerTop
          (openFirstCompositeIso U.ι g).inv).whiskerBottom
            (openFirstCompositeIso (f ⁻¹ᵁ U).ι a).hom).natTrans := rfl

-- Mate normalization elaborates dependent scheme-module composites.
theorem moduleSquareBaseChangeMap_baseOpen (M : X.Modules) :
    moduleSquareBaseChangeMap (a ≫ (f ⁻¹ᵁ U).ι) b f (g ≫ U.ι)
        (baseOpenCondition f U a b g h) M =
      (openFirstCompositeIso U.ι g).inv.app ((Scheme.Modules.pushforward f).obj M) ≫
        (Scheme.Modules.pullback g).map
          (Scheme.Modules.Pullback.OpenRestriction.restrictedPushforwardMap f U M) ≫
          moduleSquareBaseChangeMap a b (f ∣_ U) g h
            ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj M) ≫
              (Scheme.Modules.pushforward b).map
                ((openFirstCompositeIso (f ⁻¹ᵁ U).ι a).hom.app M) := by
  rw [← baseChangeNatTransOfSquare_app (a ≫ (f ⁻¹ᵁ U).ι) b f (g ≫ U.ι)
    (baseOpenCondition f U a b g h) M]
  unfold baseChangeNatTransOfSquare
  rw [← baseOpenPastedSquare_eq f U a b g h, baseOpenPastedSquare_whisker f U a b g h]
  rw [mateEquiv_whiskerBottom, mateEquiv_whiskerTop, mateEquiv_vcomp]
  · simp only [TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app, TwoSquare.vComp,
      TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app, Functor.comp_obj,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Category.id_comp,
      Category.comp_id, Category.assoc]
    rw [restrictionSquare_mate f U M]
    rw [show ((mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U))
      (Scheme.Modules.pullbackPushforwardAdjunction b)) (pullbackSquareIso a b (f ∣_ U) g
        h).hom).app
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj M) =
      moduleSquareBaseChangeMap a b (f ∣_ U) g h
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj M) from
          baseChangeNatTransOfSquare_app a b (f ∣_ U) g h _]

theorem moduleSquareBaseChangeMap_baseOpen_isIso (M : X.Modules)
    [IsIso (moduleSquareBaseChangeMap a b (f ∣_ U) g h
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ U).ι).obj M))] :
    IsIso (moduleSquareBaseChangeMap (a ≫ (f ⁻¹ᵁ U).ι) b f (g ≫ U.ι)
      (baseOpenCondition f U a b g h) M) := by
  rw [moduleSquareBaseChangeMap_baseOpen f U a b g h M]
  letI := Scheme.Modules.Pullback.OpenRestriction.restrictedPushforwardMap_isIso f U M
  infer_instance

omit h in
-- Strip only the genuine open-restriction isomorphisms from the exact mate identity.
theorem moduleSquareBaseChangeMap_testOpen_isIso {P X Y T : Scheme.{u}}
    (a : P ⟶ X) (b : P ⟶ T) (f : X ⟶ Y) (g : T ⟶ Y)
    (h : a ≫ f = b ≫ g) (W : T.Opens) (M : X.Modules)
    (hlocal : IsIso (moduleSquareBaseChangeMap ((b ⁻¹ᵁ W).ι ≫ a) (b ∣_ W) f (W.ι ≫ g)
      (testOpenCondition a b f g h W) M)) :
    IsIso ((Scheme.Modules.restrictFunctor W.ι).map (moduleSquareBaseChangeMap a b f g h M)) := by
  rw [moduleSquareBaseChangeMap_testOpen a b f g h W M] at hlocal
  letI := Scheme.Modules.Pullback.OpenRestriction.restrictedPushforwardMap_isIso b W
    ((Scheme.Modules.pullback a).obj M)
  simpa only [isIso_comp_left_iff, isIso_comp_right_iff] using hlocal

end AlgebraicGeometry.Scheme.Modules.BaseChange.Affine.Square
