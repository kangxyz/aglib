/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.PullbackSections
public import Aglib.AlgebraicGeometry.Modules.Pushforward.Isomorphism
public import Aglib.AlgebraicGeometry.Modules.IsomorphismFunctors

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
