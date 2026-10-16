/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pullback
public import Aglib.AlgebraicGeometry.Modules.Pullback.OpenRestriction
public import Aglib.CategoryTheory.Adjunction.Mates

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.PullbackSections
public import Aglib.AlgebraicGeometry.Modules.Pushforward.Isomorphism
public import Aglib.AlgebraicGeometry.Modules.IsomorphismFunctors

/-!
# Affine global sections and pullback

The actual top-open evaluation and affine tilde adjunction preserve their
original units. The `BaseChange.Affine` block uses restriction and literal
top evaluation. The `Scheme.Modules` block uses pullback and spectrum-global
sections; those original right adjoints and units are retained separately. Quasicoherence,
the actual GammaSpec map and all original
universes are retained; no affine-base-change input is assumed.

Source: `R5Lab/AlgebraicGeometry/Curves/Degree/AffineModuleBaseChange.lean`, frozen R5 integration
`79307ff88f07d34fd5c3edb859f799c55e38f290`, SHA-256
`0739a4c1e7297a8f1dec99f8f53914339710e9240fa56c70a90ae2127581ed06`. Selected original ranges: [[417,
576], [793, 803], [904, 922]].
-/

@[expose] public section
noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry Opposite Module TopologicalSpace
attribute [local instance] AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pushforward
namespace AlgebraicGeometry.Scheme.Modules.BaseChange.Affine
universe u

/-- Global sections of the actual direct image agree with global sections on the source. -/
def globalPushforwardΓIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    Scheme.Modules.pushforward f ⋙ (SheafOfModules.evaluation Y.ringCatSheaf (op ⊤)) ≅
      (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)) ⋙ ModuleCat.restrictScalars f.appTop.hom
        := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · exact Iso.refl _
  · intro M N a
    ext x
    rfl

/-- The tilde functor on an affine scheme, transported through its canonical spectrum comparison. -/
def affineTildeFunctor (X : Scheme.{u}) [IsAffine X] :
    ModuleCat.{u} Γ(X, ⊤) ⥤ X.Modules :=
  tilde.functor Γ(X, ⊤) ⋙ Scheme.Modules.restrictFunctor X.isoSpec.hom

/-- The global-sections comparison for the transported affine tilde functor. -/
def affineTildeΓRightIso (X : Scheme.{u}) [IsAffine X] :
    Scheme.Modules.pushforward X.isoSpec.hom ⋙ moduleSpecΓFunctor ≅
      (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)) := by
  refine NatIso.ofComponents (fun M ↦ ?_) ?_
  · let φ := X.isoSpec.hom.appTop.hom.comp (Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom
    have h : φ = RingHom.id _ := by
      dsimp [φ]
      rw [← CommRingCat.hom_comp]
      simp [Scheme.isoSpec_hom, Scheme.toSpecΓ_appTop]
    exact (ModuleCat.restrictScalarsComp'App
      (Scheme.ΓSpecIso Γ(X, ⊤)).inv.hom X.isoSpec.hom.appTop.hom φ rfl
      (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤))).obj M)).symm ≪≫
      (ModuleCat.restrictScalarsId' φ h).app (((SheafOfModules.evaluation X.ringCatSheaf (op
        ⊤))).obj M)
  · intro M N f
    ext x
    rfl

/-- The tilde/global-sections adjunction transported to the actual affine scheme. -/
def affineTildeAdjunction (X : Scheme.{u}) [IsAffine X] :
    affineTildeFunctor X ⊣ (SheafOfModules.evaluation X.ringCatSheaf (op ⊤)) :=
  ((tilde.adjunction (R := Γ(X, ⊤))).comp
    (Scheme.Modules.restrictAdjunction X.isoSpec.hom)).ofNatIsoRight (affineTildeΓRightIso X)

/-- The canonical comparison between restriction and direct image along a scheme isomorphism. -/
def isoRestrictPushforwardComparison {X Y : Scheme.{u}} (e : X ≅ Y) (M : Y.Modules) :
    M.restrict e.hom ≅ (Scheme.Modules.pushforward e.inv).obj M := by
  let a : (Scheme.Modules.pushforward e.hom).obj
      ((Scheme.Modules.pushforward e.inv).obj M) ≅ M :=
    ((Scheme.Modules.pushforwardComp e.inv e.hom).app M) ≪≫
      ((Scheme.Modules.pushforwardCongr e.inv_hom_id).app M) ≪≫
      ((Scheme.Modules.pushforwardId Y).app M)
  exact (Scheme.Modules.restrictFunctor e.hom).mapIso a.symm ≪≫
    (Scheme.Modules.restrictFunctorAdjCounitIso e.hom).app _

instance isoPushforwardQuasicoherent {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f]
    (M : X.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    (isoRestrictPushforwardComparison (asIso f).symm M) inferInstance

instance affineTilde_counit_isIso (X : Scheme.{u}) [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] :
    IsIso ((affineTildeAdjunction X).counit.app M) := by
  haveI : IsIso ((tilde.adjunction (R := Γ(X, ⊤))).counit.app
    ((Scheme.Modules.pushforward X.isoSpec.hom).obj M)) :=
    inferInstanceAs (IsIso ((Scheme.Modules.pushforward X.isoSpec.hom).obj M).fromTildeΓ)
  change IsIso ((affineTildeFunctor X).map ((affineTildeΓRightIso X).inv.app M) ≫
    (Scheme.Modules.restrictFunctor X.isoSpec.hom).map
      ((tilde.adjunction (R := Γ(X, ⊤))).counit.app _) ≫
    (Scheme.Modules.restrictAdjunction X.isoSpec.hom).counit.app M)
  infer_instance

/-- The tilde counit isomorphism for an actual quasi-coherent module on an affine scheme. -/
def affineTildeCounitIso (X : Scheme.{u}) [IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] :
    (affineTildeFunctor X).obj (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤))).obj M) ≅ M :=
  asIso ((affineTildeAdjunction X).counit.app M)

/-- The tilde/pullback comparison induced by the canonical adjunction data. -/
def affinePullbackTildeComparison {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    affineTildeFunctor Y ⋙ Scheme.Modules.pullback f ≅
      ModuleCat.extendScalars f.appTop.hom ⋙ affineTildeFunctor X :=
  Adjunction.leftAdjointUniq
    (((affineTildeAdjunction Y).comp (Scheme.Modules.pullbackPushforwardAdjunction f)).ofNatIsoRight
      (globalPushforwardΓIso f))
    ((ModuleCat.extendRestrictScalarsAdj f.appTop.hom).comp (affineTildeAdjunction X))

instance affinePullbackQuasicoherent {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pullback f).obj M).IsQuasicoherent := by
  let e : (Scheme.Modules.pullback f).obj M ≅
      (affineTildeFunctor X).obj ((ModuleCat.extendScalars f.appTop.hom).obj
        (((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤))).obj M)) :=
    (Scheme.Modules.pullback f).mapIso (affineTildeCounitIso Y M).symm ≪≫
      (affinePullbackTildeComparison f).app _
  have hqc : ((affineTildeFunctor X).obj ((ModuleCat.extendScalars f.appTop.hom).obj
      (((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤))).obj M))).IsQuasicoherent := by
    change ((tilde.functor Γ(X, ⊤)).obj _).restrict X.isoSpec.hom |>.IsQuasicoherent
    infer_instance
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso e.symm hqc

instance affinePushforwardQuasicoherent {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (M : X.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj M).IsQuasicoherent := by
  have h : f = X.isoSpec.hom ≫ Spec.map f.appTop ≫ Y.isoSpec.inv := by
    rw [← Category.assoc, Scheme.isoSpec_hom_naturality]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  let e : (Scheme.Modules.pushforward f).obj M ≅
      (Scheme.Modules.pushforward Y.isoSpec.inv).obj
        ((Scheme.Modules.pushforward (Spec.map f.appTop)).obj
          ((Scheme.Modules.pushforward X.isoSpec.hom).obj M)) :=
    (Scheme.Modules.pushforwardCongr h).app M ≪≫
      ((Scheme.Modules.pushforwardComp X.isoSpec.hom (Spec.map f.appTop ≫ Y.isoSpec.inv)).app
        M).symm ≪≫
      ((Scheme.Modules.pushforwardComp (Spec.map f.appTop) Y.isoSpec.inv).app _).symm
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso e.symm inferInstance

theorem affineΓ_isIso_of_quasicoherent {X : Scheme.{u}} [IsAffine X]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (a : M ⟶ N) [IsIso (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤))).map a)] : IsIso a := by
  let A := affineTildeAdjunction X
  have h : A.counit.app M ≫ a =
      (affineTildeFunctor X).map (((SheafOfModules.evaluation X.ringCatSheaf (op ⊤))).map a) ≫
        A.counit.app N :=
    by simpa only [Functor.comp_map, Functor.id_map] using (A.counit.naturality a).symm
  haveI : IsIso ((affineTildeFunctor X).map (((SheafOfModules.evaluation X.ringCatSheaf (op
    ⊤))).map a) ≫ A.counit.app N) :=
    inferInstance
  haveI : IsIso (A.counit.app M ≫ a) := h.symm ▸ inferInstance
  exact (isIso_comp_left_iff (A.counit.app M) a).mp inferInstance

instance isoRestrict_reflectsIsomorphisms {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    (Scheme.Modules.restrictFunctor f).ReflectsIsomorphisms := by
  let e := asIso f
  let c : Scheme.Modules.restrictFunctor e.hom ⋙ Scheme.Modules.restrictFunctor e.inv ≅ 𝟭 _ :=
    (Scheme.Modules.restrictFunctorComp e.inv e.hom).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.inv_hom_id ≪≫ Scheme.Modules.restrictFunctorId (X := Y)
  letI : (Scheme.Modules.restrictFunctor e.hom ⋙
      Scheme.Modules.restrictFunctor e.inv).ReflectsIsomorphisms :=
    reflectsIsomorphisms_of_iso c.symm
  exact reflectsIsomorphisms_of_comp (Scheme.Modules.restrictFunctor e.hom)
    (Scheme.Modules.restrictFunctor e.inv)

instance affineTilde_reflectsIsomorphisms (X : Scheme.{u}) [IsAffine X] :
    (affineTildeFunctor X).ReflectsIsomorphisms := by
  change (tilde.functor Γ(X, ⊤) ⋙ Scheme.Modules.restrictFunctor X.isoSpec.hom).ReflectsIsomorphisms
  infer_instance

instance affineTilde_imageQuasicoherent (X : Scheme.{u}) [IsAffine X]
    (M : ModuleCat.{u} Γ(X, ⊤)) : ((affineTildeFunctor X).obj M).IsQuasicoherent := by
  change (tilde M).restrict X.isoSpec.hom |>.IsQuasicoherent
  infer_instance

instance affineTilde_unit_isIso (X : Scheme.{u}) [IsAffine X]
    (M : ModuleCat.{u} Γ(X, ⊤)) : IsIso ((affineTildeAdjunction X).unit.app M) := by
  let A := affineTildeAdjunction X
  let Φ := affineTildeFunctor X
  haveI : IsIso (A.counit.app (Φ.obj M)) := inferInstance
  have h : Φ.map (A.unit.app M) ≫ A.counit.app (Φ.obj M) = 𝟙 _ :=
    A.left_triangle_components M
  haveI : IsIso (Φ.map (A.unit.app M) ≫ A.counit.app (Φ.obj M)) := h.symm ▸ inferInstance
  haveI : IsIso (Φ.map (A.unit.app M)) :=
    (isIso_comp_right_iff (Φ.map (A.unit.app M)) (A.counit.app (Φ.obj M))).mp inferInstance
  exact isIso_of_reflects_iso (A.unit.app M) Φ

/-- The canonical scalar-extension comparison for global sections of an affine pullback. -/
def affinePullbackΓIso {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent] :
    ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤))).obj ((Scheme.Modules.pullback f).obj M) ≅
      (ModuleCat.extendScalars f.appTop.hom).obj (((SheafOfModules.evaluation Y.ringCatSheaf (op
        ⊤))).obj M) :=
  ((SheafOfModules.evaluation X.ringCatSheaf (op ⊤))).mapIso
    ((Scheme.Modules.pullback f).mapIso (affineTildeCounitIso Y M).symm ≪≫
      (affinePullbackTildeComparison f).app _) ≪≫
    (asIso ((affineTildeAdjunction X).unit.app _)).symm

theorem affinePullbackΓIso_unit {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent] :
    ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤))).map
        ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M) ≫
      (globalPushforwardΓIso f).hom.app ((Scheme.Modules.pullback f).obj M) ≫
      (ModuleCat.restrictScalars f.appTop.hom).map (affinePullbackΓIso f M).hom =
        (ModuleCat.extendRestrictScalarsAdj f.appTop.hom).unit.app
          (((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤))).obj M) :=
  adjunctionComparisonIso_unit (affineTildeAdjunction Y) (affineTildeAdjunction X)
    (Scheme.Modules.pullbackPushforwardAdjunction f)
    (ModuleCat.extendRestrictScalarsAdj f.appTop.hom) (globalPushforwardΓIso f) M

theorem affinePullbackΓIso_unit_apply {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent]
    (m : ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤))).obj M) :
    (affinePullbackΓIso f M).hom
        (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤ m) =
      (ModuleCat.extendRestrictScalarsAdj f.appTop.hom).unit.app
        (((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤))).obj M) m := by
  have hh := congrArg (fun z ↦ z m) (affinePullbackΓIso_unit f M)
  exact hh

theorem affinePullbackΓIso_inv_unit_apply {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent]
    (m : ((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤))).obj M) :
    (affinePullbackΓIso f M).inv
        ((ModuleCat.extendRestrictScalarsAdj f.appTop.hom).unit.app
          (((SheafOfModules.evaluation Y.ringCatSheaf (op ⊤))).obj M) m) =
      ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤ m := by
  rw [← affinePullbackΓIso_unit_apply f M m]
  exact (affinePullbackΓIso f M).toLinearEquiv.symm_apply_apply
    (((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤ m)

end AlgebraicGeometry.Scheme.Modules.BaseChange.Affine

/-! # Native affine sections through the canonical spectrum isomorphism

The functors are the original tilde, pullback, pushforward and spectrum-section
functors, composed with the canonical `isoSpec`. Their original adjunction is
retained, including the unit and quasicoherent counit.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- The original direct image along an isomorphism preserves quasicoherence. -/
theorem isQuasicoherent_pushforward_of_isIso {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e]
    (M : X.Modules) [M.IsQuasicoherent] : ((pushforward e).obj M).IsQuasicoherent := by
  apply (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso
    ((pushforwardIsoRestrict (asIso e)).app M).symm
  exact isQuasicoherent_restrictFunctor (inv e) M

variable (X : Scheme.{u}) [IsAffine X]

/-- Actual affine sections, transported through the canonical spectrum isomorphism. -/
def affineΓFunctor : X.Modules ⥤ ModuleCat Γ(X, ⊤) :=
  pushforward X.isoSpec.hom ⋙ moduleSpecΓFunctor

/-- The actual top-section map underlying the affine global-section functor. -/
theorem affineΓFunctor_map_apply {M N : X.Modules} (q : M ⟶ N)
    (m : (affineΓFunctor X).obj M) : (affineΓFunctor X).map q m = q.app ⊤ m := rfl

/-- Native tilde transported back through the canonical affine spectrum isomorphism. -/
def affineTildeFunctor : ModuleCat Γ(X, ⊤) ⥤ X.Modules :=
  tilde.functor Γ(X, ⊤) ⋙ pullback X.isoSpec.hom

/-- The original composite adjunction for affine tilde and actual affine sections. -/
def affineTildeAdjunction : affineTildeFunctor X ⊣ affineΓFunctor X :=
  (tilde.adjunction (R := Γ(X, ⊤))).comp (pullbackPushforwardAdjunction X.isoSpec.hom)

/-- The native affine tilde adjunction has an invertible original unit. -/
theorem affineTildeAdjunction_unit_isIso : IsIso (affineTildeAdjunction X).unit := by
  let : (pushforward X.isoSpec.hom).IsEquivalence :=
    pushforward_isEquivalence_of_isIso X.isoSpec.hom
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  change IsIso ((tilde.adjunction (R := Γ(X, ⊤))).unit.app M ≫
    moduleSpecΓFunctor.map ((pullbackPushforwardAdjunction X.isoSpec.hom).unit.app (tilde M)))
  infer_instance

/-- The original affine tilde counit is invertible on every quasicoherent sheaf. -/
theorem affineTildeAdjunction_counit_isIso (M : X.Modules) [M.IsQuasicoherent] :
    IsIso ((affineTildeAdjunction X).counit.app M) := by
  let : (pushforward X.isoSpec.hom).IsEquivalence :=
    pushforward_isEquivalence_of_isIso X.isoSpec.hom
  let := isQuasicoherent_pushforward_of_isIso X.isoSpec.hom M
  change IsIso ((pullback X.isoSpec.hom).map
      ((pushforward X.isoSpec.hom).obj M).fromTildeΓ ≫
    (pullbackPushforwardAdjunction X.isoSpec.hom).counit.app M)
  infer_instance

/-- Transported native tilde is quasicoherent on an arbitrary affine scheme. -/
theorem affineTildeFunctor_isQuasicoherent (M : ModuleCat.{u} Γ(X, ⊤)) :
    ((affineTildeFunctor X).obj M).IsQuasicoherent := by
  apply (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    ((restrictFunctorIsoPullback X.isoSpec.hom).app (tilde M))
  exact isQuasicoherent_restrictFunctor X.isoSpec.hom (tilde M)

/-- Actual affine sections detect isomorphisms between quasicoherent sheaves. -/
theorem isIso_of_affineΓFunctor_map_isIso {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent] (f : M ⟶ N)
    [IsIso ((affineΓFunctor X).map f)] : IsIso f := by
  let := affineTildeAdjunction_counit_isIso X M
  let := affineTildeAdjunction_counit_isIso X N
  have hn := (affineTildeAdjunction X).counit.naturality f
  change (affineTildeFunctor X).map ((affineΓFunctor X).map f) ≫
      (affineTildeAdjunction X).counit.app N =
    (affineTildeAdjunction X).counit.app M ≫ f at hn
  have : IsIso ((affineTildeAdjunction X).counit.app M ≫ f) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_left ((affineTildeAdjunction X).counit.app M) f

variable {X} {Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y)

/-- The original direct image on arbitrary affine schemes is scalar restriction on sections. -/
def affinePushforwardGlobalSectionsIso :
    pushforward f ⋙ affineΓFunctor Y ≅
      affineΓFunctor X ⋙ ModuleCat.restrictScalars f.appTop.hom :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (pushforwardComp f Y.isoSpec.hom ≪≫
        pushforwardCongr (Scheme.isoSpec_hom_naturality f).symm ≪≫
        (pushforwardComp X.isoSpec.hom (Spec.map f.appTop)).symm)
      moduleSpecΓFunctor ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (pushforward X.isoSpec.hom)
      (pushforwardGlobalSectionsIso f.appTop) ≪≫
    (Functor.associator _ _ _).symm

/-- The native affine direct-image comparison is the identity on actual top sections. -/
theorem affinePushforwardGlobalSectionsIso_hom_apply (M : X.Modules)
    (m : (affineΓFunctor Y).obj ((pushforward f).obj M)) :
    (affinePushforwardGlobalSectionsIso f).hom.app M m = m := by
  simp only [Functor.comp_obj]
  change M.presheaf.map (𝟙 (.op (⊤ : X.Opens))) m = m
  simp

/-- The inverse affine direct-image comparison is also the identity on actual top sections. -/
theorem affinePushforwardGlobalSectionsIso_inv_apply (M : X.Modules)
    (m : (ModuleCat.restrictScalars f.appTop.hom).obj ((affineΓFunctor X).obj M)) :
    (affinePushforwardGlobalSectionsIso f).inv.app M m = m := by
  have hi := congrArg (fun q => q m) ((affinePushforwardGlobalSectionsIso f).inv_hom_id_app M)
  simpa only [ModuleCat.comp_apply, ModuleCat.id_apply,
    affinePushforwardGlobalSectionsIso_hom_apply] using hi

/-- Direct image between arbitrary affine schemes preserves quasicoherence. -/
theorem isQuasicoherent_pushforward_of_isAffine (M : X.Modules) [M.IsQuasicoherent] :
    ((pushforward f).obj M).IsQuasicoherent := by
  let := isQuasicoherent_pushforward_of_isIso X.isoSpec.hom M
  let := isQuasicoherent_pushforward f.appTop ((pushforward X.isoSpec.hom).obj M)
  have h := isQuasicoherent_pushforward_of_isIso Y.isoSpec.inv
    ((pushforward (Spec.map f.appTop)).obj ((pushforward X.isoSpec.hom).obj M))
  let e : (pushforward Y.isoSpec.inv).obj
        ((pushforward (Spec.map f.appTop)).obj ((pushforward X.isoSpec.hom).obj M)) ≅
      (pushforward f).obj M :=
    (pushforward Y.isoSpec.inv).mapIso
        ((pushforwardComp X.isoSpec.hom (Spec.map f.appTop)).app M) ≪≫
      (pushforwardComp (X.isoSpec.hom ≫ Spec.map f.appTop) Y.isoSpec.inv).app M ≪≫
      (pushforwardCongr (by rw [Scheme.isoSpec_hom_naturality f, Category.assoc,
        Iso.hom_inv_id, Category.comp_id])).app M
  exact (SheafOfModules.isQuasicoherent Y.ringCatSheaf).prop_of_iso e h

end AlgebraicGeometry.Scheme.Modules
