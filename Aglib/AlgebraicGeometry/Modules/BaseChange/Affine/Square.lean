/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.Basic
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.GlobalSections
public import Aglib.Algebra.Category.ModuleCat.BaseChange

/-!
# Affine cartesian-square module mates

The square map is the mate of the actual pullback square and counit.
For the native pullback square it is definitionally the existing
moduleBaseChangeMap; its actual affine Gamma map is the scalar-pushout mate.

Source: `R5Lab/AlgebraicGeometry/Curves/Degree/AffineModuleBaseChange.lean`, frozen R5 integration
`79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`0739a4c1e7297a8f1dec99f8f53914339710e9240fa56c70a90ae2127581ed06`. Selected original ranges: [[642,
785], [809, 831], [868, 878], [885, 899], [944, 980], [993, 1019]].
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry Opposite Module TopologicalSpace
namespace AlgebraicGeometry.Scheme.Modules.BaseChange.Affine.Square
universe u
variable {P X Y T : Scheme.{u}}

/-- The pullback functor isomorphism determined by the displayed commutative scheme square. -/
def pullbackSquareIso (a : P ⟶ X) (b : P ⟶ T) (f : X ⟶ Y) (g : T ⟶ Y)
    (h : a ≫ f = b ≫ g) :
    Scheme.Modules.pullback g ⋙ Scheme.Modules.pullback b ≅
      Scheme.Modules.pullback f ⋙ Scheme.Modules.pullback a :=
  Scheme.Modules.pullbackComp b g ≪≫ Scheme.Modules.pullbackCongr h.symm ≪≫
    (Scheme.Modules.pullbackComp a f).symm

/-- The actual adjunction mate for the displayed commutative square and module sheaf. -/
def moduleSquareBaseChangeMap (a : P ⟶ X) (b : P ⟶ T) (f : X ⟶ Y) (g : T ⟶ Y)
    (h : a ≫ f = b ≫ g) (M : X.Modules) :
    (Scheme.Modules.pullback g).obj ((Scheme.Modules.pushforward f).obj M) ⟶
      (Scheme.Modules.pushforward b).obj ((Scheme.Modules.pullback a).obj M) :=
  (Scheme.Modules.pullbackPushforwardAdjunction b).homEquiv _ _
    ((pullbackSquareIso a b f g h).hom.app _ ≫
      (Scheme.Modules.pullback a).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M))

theorem moduleSquareBaseChangeMap_eq (f : X ⟶ Y) (g : T ⟶ Y) (M : X.Modules) :
    moduleSquareBaseChangeMap (pullback.fst f g) (pullback.snd f g) f g pullback.condition M =
      moduleBaseChangeMap f g M := rfl

/-- The natural transformation obtained as the mate of the pullback-square isomorphism. -/
def baseChangeNatTransOfSquare (a : P ⟶ X) (b : P ⟶ T) (f : X ⟶ Y) (g : T ⟶ Y)
    (h : a ≫ f = b ≫ g) :
    Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback g ⟶
      Scheme.Modules.pullback a ⋙ Scheme.Modules.pushforward b :=
  (mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction b))
    ((pullbackSquareIso a b f g h).hom)

theorem baseChangeNatTransOfSquare_app (a : P ⟶ X) (b : P ⟶ T)
    (f : X ⟶ Y) (g : T ⟶ Y) (h : a ≫ f = b ≫ g) (M : X.Modules) :
    (baseChangeNatTransOfSquare a b f g h).app M =
      moduleSquareBaseChangeMap a b f g h M := by
  unfold moduleSquareBaseChangeMap baseChangeNatTransOfSquare
  rw [Adjunction.homEquiv_unit]
  simp only [mateEquiv, TwoSquare.mk, TwoSquare.natTrans, Equiv.coe_fn_mk,
    NatTrans.comp_app, Functor.leftUnitor_hom_app, Functor.rightUnitor_inv_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.comp_map, Category.id_comp]
  rw [Functor.map_comp]
  simp only [Functor.comp_obj, Category.id_comp]
  erw [Category.comp_id]



theorem restrictionSquare_mate (f : X ⟶ Y) (U : Y.Opens) (M : X.Modules) :
    ((mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)))
      (Scheme.Modules.Pullback.OpenRestriction.localPullbackIso f U).inv).app M =
      Scheme.Modules.Pullback.OpenRestriction.restrictedPushforwardMap f U M := by
  let α := (Scheme.Modules.Pullback.OpenRestriction.localPullbackIso f U).inv
  let A := Scheme.Modules.pullbackPushforwardAdjunction (f ∣_ U)
  apply (A.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit]
  rw [mateEquiv_counit]
  have hc : ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).symm
      (𝟙 ((Scheme.Modules.pushforward f).obj M)) =
        (Scheme.Modules.pullbackPushforwardAdjunction f).counit.app M := by
    rw [Adjunction.homEquiv_counit]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
  have h := Scheme.Modules.Pullback.OpenRestriction.restrictedAdjoint_eq f U
    (φ := 𝟙 ((Scheme.Modules.pushforward f).obj M))
  rw [hc] at h
  erw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  apply (cancel_epi ((Scheme.Modules.Pullback.OpenRestriction.localPullbackIso f U).hom.app
    ((Scheme.Modules.pushforward f).obj M))).mp
  erw [← Category.assoc, Iso.hom_inv_id_app, Category.id_comp]
  exact h


theorem testOpenPastedMate (a : P ⟶ X) (b : P ⟶ T) (f : X ⟶ Y) (g : T ⟶ Y)
    (h : a ≫ f = b ≫ g) (U : T.Opens) (M : X.Modules) :
    ((mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackPushforwardAdjunction (b ∣_ U)))
      (TwoSquare.hComp (pullbackSquareIso a b f g h).hom
        (Scheme.Modules.Pullback.OpenRestriction.localPullbackIso b U).inv)).app M =
      (Scheme.Modules.restrictFunctor U.ι).map (moduleSquareBaseChangeMap a b f g h M) ≫
        Scheme.Modules.Pullback.OpenRestriction.restrictedPushforwardMap b U
          ((Scheme.Modules.pullback a).obj M) := by
  rw [mateEquiv_vcomp]
  · simp only [TwoSquare.vComp, TwoSquare.mk, TwoSquare.natTrans, NatTrans.comp_app,
      Functor.associator_hom_app, Functor.associator_inv_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Category.id_comp, Category.comp_id]
    rw [restrictionSquare_mate]
    rw [← baseChangeNatTransOfSquare_app]
    rfl



theorem conjugateEquiv_pullbackComp_hom {Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction f))
      (Scheme.Modules.pullbackComp f g).hom = (Scheme.Modules.pushforwardComp f g).inv := by
  apply (cancel_mono (Scheme.Modules.pushforwardComp f g).hom).mp
  rw [← Scheme.Modules.conjugateEquiv_pullbackComp_inv]
  rw [conjugateEquiv_comm _ _ (Iso.inv_hom_id (Scheme.Modules.pullbackComp f g))]
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv]
  exact (Scheme.Modules.pushforwardComp f g).inv_hom_id.symm

theorem conjugateEquiv_pullbackCongr {f g : X ⟶ Y} (h : f = g) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction g)
      (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Scheme.Modules.pullbackCongr h).hom = (Scheme.Modules.pushforwardCongr h).inv := by
  cases h
  change conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction f) (𝟙 _) = _
  rw [conjugateEquiv_id]
  ext M U x
  simp only [NatTrans.id_app, Scheme.Modules.Hom.id_app,
    Scheme.Modules.pushforwardCongr_inv_app_app]
  change x = M.presheaf.map (𝟙 _) x
  rw [M.presheaf.map_id]
  rfl

theorem pushforwardCongr_symm_inv {f g : X ⟶ Y} (h : f = g) :
    (Scheme.Modules.pushforwardCongr h.symm).inv =
      (Scheme.Modules.pushforwardCongr h).hom := by
  cases h
  ext M U x
  rfl

/-- The direct-image functor isomorphism determined by the displayed commutative square. -/
def pushforwardSquareIso (a : P ⟶ X) (b : P ⟶ T) (f : X ⟶ Y) (g : T ⟶ Y)
    (h : a ≫ f = b ≫ g) :
    Scheme.Modules.pushforward a ⋙ Scheme.Modules.pushforward f ≅
      Scheme.Modules.pushforward b ⋙ Scheme.Modules.pushforward g :=
  Scheme.Modules.pushforwardComp a f ≪≫ Scheme.Modules.pushforwardCongr h ≪≫
    (Scheme.Modules.pushforwardComp b g).symm

theorem conjugateEquiv_pullbackSquareIso (a : P ⟶ X) (b : P ⟶ T)
    (f : X ⟶ Y) (g : T ⟶ Y) (h : a ≫ f = b ≫ g) :
    conjugateEquiv
      ((Scheme.Modules.pullbackPushforwardAdjunction f).comp
        (Scheme.Modules.pullbackPushforwardAdjunction a))
      ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
        (Scheme.Modules.pullbackPushforwardAdjunction b))
      (pullbackSquareIso a b f g h).hom = (pushforwardSquareIso a b f g h).hom := by
  unfold pullbackSquareIso pushforwardSquareIso
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc]
  rw [← conjugateEquiv_comp _ (Scheme.Modules.pullbackPushforwardAdjunction (a ≫ f)) _]
  rw [← conjugateEquiv_comp _ (Scheme.Modules.pullbackPushforwardAdjunction (b ≫ g)) _]
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, conjugateEquiv_pullbackCongr,
    conjugateEquiv_pullbackComp_hom]
  rfl

theorem moduleSquareBaseChangeMap_homEquiv (a : P ⟶ X) (b : P ⟶ T)
    (f : X ⟶ Y) (g : T ⟶ Y) (h : a ≫ f = b ≫ g) (M : X.Modules) :
    (Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv _ _
      (moduleSquareBaseChangeMap a b f g h M) =
      (Scheme.Modules.pushforward f).map
        ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M) ≫
      (pushforwardSquareIso a b f g h).hom.app ((Scheme.Modules.pullback a).obj M) := by
  have hh := iterated_mateEquiv_conjugateEquiv
    (Scheme.Modules.pullbackPushforwardAdjunction f)
    (Scheme.Modules.pullbackPushforwardAdjunction b)
    (Scheme.Modules.pullbackPushforwardAdjunction g)
    (Scheme.Modules.pullbackPushforwardAdjunction a) (pullbackSquareIso a b f g h).hom
  rw [conjugateEquiv_pullbackSquareIso] at hh
  have hm := unit_mateEquiv
    (Scheme.Modules.pullbackPushforwardAdjunction a)
    (Scheme.Modules.pullbackPushforwardAdjunction g)
    (baseChangeNatTransOfSquare a b f g h) M
  have happ := congrArg (fun z ↦ z.app ((Scheme.Modules.pullback a).obj M)) hh
  change ((mateEquiv (Scheme.Modules.pullbackPushforwardAdjunction a)
    (Scheme.Modules.pullbackPushforwardAdjunction g)
    (baseChangeNatTransOfSquare a b f g h)).app _) = _ at happ
  rw [happ, baseChangeNatTransOfSquare_app] at hm
  exact hm.symm

theorem pushforwardSquareIso_appTop (a : P ⟶ X) (b : P ⟶ T)
    (f : X ⟶ Y) (g : T ⟶ Y) (h : a ≫ f = b ≫ g) (N : P.Modules)
    (m : N.presheaf.obj (op ⊤)) :
    ((pushforwardSquareIso a b f g h).hom.app N).app ⊤ m = m := by
  simp only [pushforwardSquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Scheme.Modules.Hom.comp_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app, Scheme.Modules.pushforwardCongr_hom_app_app,
    Category.id_comp, Category.comp_id]
  change N.presheaf.map (𝟙 (op (⊤ : P.Opens))) m = m
  rw [N.presheaf.map_id]
  rfl

theorem moduleSquareBaseChangeMap_unit_appTop (a : P ⟶ X) (b : P ⟶ T)
    (f : X ⟶ Y) (g : T ⟶ Y) (h : a ≫ f = b ≫ g) (M : X.Modules)
    (m : M.presheaf.obj (op ⊤)) :
    (moduleSquareBaseChangeMap a b f g h M).app ⊤
      (((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        ((Scheme.Modules.pushforward f).obj M)).app ⊤ m) =
      ((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app ⊤ m := by
  have hh := moduleSquareBaseChangeMap_homEquiv a b f g h M
  rw [Adjunction.homEquiv_unit] at hh
  have ht := congrArg (fun z ↦ z.app ⊤ m) hh
  change (moduleSquareBaseChangeMap a b f g h M).app ⊤ _ =
    ((pushforwardSquareIso a b f g h).hom.app _).app ⊤
      (((Scheme.Modules.pullbackPushforwardAdjunction a).unit.app M).app ⊤ m) at ht
  rw [pushforwardSquareIso_appTop] at ht
  exact ht

theorem evaluation_top_map_apply {Z : Scheme.{u}} {M N : Z.Modules}
    (c : M ⟶ N) (m : ((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤))).obj M) :
    ((SheafOfModules.evaluation Z.ringCatSheaf (op ⊤))).map c m = c.app ⊤ m := rfl

/-- The actual square mate in affine global sections, transported by the canonical
pullback/global-section comparisons. -/
def affineSquareΓBaseChangeMap [IsAffine P] [IsAffine X] [IsAffine Y] [IsAffine T]
    (a : P ⟶ X) (b : P ⟶ T) (f : X ⟶ Y) (g : T ⟶ Y)
    (h : a ≫ f = b ≫ g) (M : X.Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendScalars g.appTop.hom).obj
      ((ModuleCat.restrictScalars f.appTop.hom).obj (((SheafOfModules.evaluation X.ringCatSheaf
        (op ⊤))).obj M)) ⟶
    (ModuleCat.restrictScalars b.appTop.hom).obj
      ((ModuleCat.extendScalars a.appTop.hom).obj (((SheafOfModules.evaluation X.ringCatSheaf (op
        ⊤))).obj M)) :=
  (affinePullbackΓIso g ((Scheme.Modules.pushforward f).obj M)).inv ≫
    ((SheafOfModules.evaluation T.ringCatSheaf (op ⊤))).map (moduleSquareBaseChangeMap a b f g h
      M) ≫
    (ModuleCat.restrictScalars b.appTop.hom).map (affinePullbackΓIso a M).hom

theorem affineSquareΓBaseChangeMap_eq [IsAffine P] [IsAffine X] [IsAffine Y] [IsAffine T]
    (a : P ⟶ X) (b : P ⟶ T) (f : X ⟶ Y) (g : T ⟶ Y)
    (h : a ≫ f = b ≫ g) (M : X.Modules) [M.IsQuasicoherent] :
    affineSquareΓBaseChangeMap a b f g h M =
      ModuleCat.baseChangeMap f.appTop g.appTop a.appTop b.appTop
        (by simpa only [Scheme.Hom.comp_appTop] using congrArg Scheme.Hom.appTop h)
        (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤))).obj M) := by
  apply ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).homEquiv _ _).injective
  ext m
  rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
    ModuleCat.extendRestrictScalarsAdj_homEquiv_apply]
  rw [← ModuleCat.extendRestrictScalarsAdj_unit_app_apply g.appTop.hom
    ((ModuleCat.restrictScalars f.appTop.hom).obj (((SheafOfModules.evaluation X.ringCatSheaf (op
      ⊤))).obj M)) m]
  rw [ModuleCat.baseChangeMap_unit_apply]
  simp only [affineSquareΓBaseChangeMap, ConcreteCategory.comp_apply]
  erw [evaluation_top_map_apply]
  erw [affinePullbackΓIso_inv_unit_apply g ((Scheme.Modules.pushforward f).obj M) m]
  rw [moduleSquareBaseChangeMap_unit_appTop]
  erw [ModuleCat.restrictScalars.map_apply]
  exact affinePullbackΓIso_unit_apply a M m

theorem moduleSquareBaseChangeMap_globalSections_isIso_affine
    [IsAffine P] [IsAffine X] [IsAffine Y] [IsAffine T]
    (a : P ⟶ X) (b : P ⟶ T) (f : X ⟶ Y) (g : T ⟶ Y)
    (H : IsPullback a b f g) (M : X.Modules) [M.IsQuasicoherent] :
    IsIso (((SheafOfModules.evaluation T.ringCatSheaf (op ⊤))).map (moduleSquareBaseChangeMap a b
      f g H.w M)) := by
  have hG := isPushout_appTop_of_isPullback H
  haveI : IsIso (affineSquareΓBaseChangeMap a b f g H.w M) := by
    rw [affineSquareΓBaseChangeMap_eq]
    exact ModuleCat.baseChangeMap_isIso _ _ _ _ hG _
  let eS := affinePullbackΓIso g ((Scheme.Modules.pushforward f).obj M)
  let eT := (ModuleCat.restrictScalars b.appTop.hom).mapIso (affinePullbackΓIso a M)
  let c := ((SheafOfModules.evaluation T.ringCatSheaf (op ⊤))).map (moduleSquareBaseChangeMap a b
    f g H.w M)
  haveI : IsIso (eS.inv ≫ c ≫ eT.hom) := by
    change IsIso (affineSquareΓBaseChangeMap a b f g H.w M)
    infer_instance
  exact isIso_of_iso_whiskers eS.symm eT c
    (by change IsIso (eS.inv ≫ c ≫ eT.hom); infer_instance)

/-- Arbitrary base change of a quasi-coherent module for a cartesian square of
affine schemes, for the actual adjunction mate. -/
theorem moduleSquareBaseChangeMap_isIso_affine
    [IsAffine P] [IsAffine X] [IsAffine Y] [IsAffine T]
    (a : P ⟶ X) (b : P ⟶ T) (f : X ⟶ Y) (g : T ⟶ Y)
    (H : IsPullback a b f g) (M : X.Modules) [M.IsQuasicoherent] :
    IsIso (moduleSquareBaseChangeMap a b f g H.w M) := by
  haveI := moduleSquareBaseChangeMap_globalSections_isIso_affine a b f g H M
  exact affineΓ_isIso_of_quasicoherent (moduleSquareBaseChangeMap a b f g H.w M)

end AlgebraicGeometry.Scheme.Modules.BaseChange.Affine.Square
