/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.Duality.Projective.Relative.NormalSurface.Trace.LocalEvaluation
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback

/-!
# Localized inverse trace and original affine evaluation

The ordinary pullback of an inverse trace is expressed through the actual
localized trace and the original tilde and geometric counits. The proof uses
naturality of those counits, never faithfulness of global sections on a
non-affine scheme. No later local ring is assumed finite over an initial base.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

namespace AlgebraicGeometry.Scheme.Cohomology

/-- Sheafification of the original coefficient stalk identifies with its actual
pullback to the local spectrum, using the original tilde counit. -/
def canonicalLocalSpectrumCoefficientIso (Y : Scheme.{u}) (y : Y)
    (L : Y.Modules) [L.IsQuasicoherent] :
    tilde ((moduleStalk Y y).obj L) ≅ (Scheme.Modules.pullback (Y.fromSpecStalk y)).obj L :=
  (tilde.functor (Y.presheaf.stalk y)).mapIso (stalkFromSpecStalkSectionsIso Y y L) ≪≫
    asIso ((Scheme.Modules.pullback (Y.fromSpecStalk y)).obj L).fromTildeΓ

/-- The original evaluation on a scheme over an affine base is the tilde
counit followed by the original geometric pullback/pushforward counit. -/
def canonicalAffineSectionsEvaluation {A : CommRingCat.{u}} {W : Scheme.{u}}
    (b : W ⟶ Spec A) (N : W.Modules) :
    (Scheme.Modules.pullback b).obj (tilde (moduleSpecΓFunctor.obj ((pushforward b).obj N))) ⟶
      N :=
  (Scheme.Modules.pullback b).map ((pushforward b).obj N).fromTildeΓ ≫
    (pullbackPushforwardAdjunction b).counit.app N

/-- The localized inverse trace, written as a map into the actual affine-base
sections of the direct image. The comparison is the original sections map. -/
def canonicalLocalInverseTraceSections
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (L : Y.Modules)
    (τ : (pushforward f).obj M ⟶ L) [IsIso τ] (y : Y) :
    (moduleStalk Y y).obj L ⟶ moduleSpecΓFunctor.obj
      ((pushforward (Limits.pullback.snd f (Y.fromSpecStalk y))).obj
        ((Scheme.Modules.pullback (Limits.pullback.fst f (Y.fromSpecStalk y))).obj M)) :=
  ModuleCat.ofHom (ordinaryPushforwardIsoOnLocalSections f M L τ y).symm.toLinearMap ≫
    (moduleSpecPushforwardGlobalSectionsIso (Limits.pullback.snd f (Y.fromSpecStalk y))).inv.app _

/-- The actual inverse localized trace is the original base-change mate on
sections, with the original stalk-to-local-sections comparison. -/
theorem canonicalLocalInverseTraceSections_normalization
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (L : Y.Modules)
    (τ : (pushforward f).obj M ⟶ L) [IsIso τ] (y : Y) :
    let j := Y.fromSpecStalk y
    let a := Limits.pullback.fst f j
    let b := Limits.pullback.snd f j
    (stalkFromSpecStalkSectionsIso Y y L).hom ≫
        moduleSpecΓFunctor.map ((Scheme.Modules.pullback j).map (inv τ) ≫
          (cartesianBaseChangeMap a b f j (IsPullback.of_hasPullback f j)).app M) =
      canonicalLocalInverseTraceSections f M L τ y := by
  let j := Y.fromSpecStalk y
  let a := Limits.pullback.fst f j
  let b := Limits.pullback.snd f j
  let N := (Scheme.Modules.pullback a).obj M
  let p := (moduleSpecPushforwardGlobalSectionsIso b).app N
  apply (cancel_mono p.hom).mp
  ext s
  have he := ordinaryPushforwardIsoOnLocalSections_symm_evaluation f M L τ y s
  have hi := ConcreteCategory.congr_hom p.inv_hom_id
    ((ordinaryPushforwardIsoOnLocalSections f M L τ y).symm s)
  simp only [ModuleCat.comp_apply, ModuleCat.id_apply] at hi
  have h := he.symm.trans hi.symm
  dsimp +instances only [p, N, b, a, j, canonicalLocalInverseTraceSections] at h ⊢
  simp only [ModuleCat.comp_apply, Iso.app_hom, Iso.app_inv] at h ⊢
  dsimp only [ModuleCat.ofHom, ConcreteCategory.hom, ConcreteCategory.ofHom] at h ⊢
  exact h

/-- The actual localized canonical pullback is original affine evaluation after
sheafification of the inverse localized trace. The hypothesis is invertibility
of the actual trace; properness does not manufacture it. -/
theorem ordinaryTracePullback_local_evaluation
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (M : X.Modules) [M.IsQuasicoherent] (L : Y.Modules) [L.IsQuasicoherent]
    (τ : (pushforward f).obj M ⟶ L) [IsIso τ] (y : Y) :
    let j := Y.fromSpecStalk y
    let a := Limits.pullback.fst f j
    let b := Limits.pullback.snd f j
    (Scheme.Modules.pullback a).map (ordinaryTracePullback f τ) =
      (ordinaryTracePullbackSquareIso a b f j (IsPullback.of_hasPullback f j)).hom.app L ≫
        (Scheme.Modules.pullback b).map (canonicalLocalSpectrumCoefficientIso Y y L).inv ≫
        (Scheme.Modules.pullback b).map
          ((tilde.functor (Y.presheaf.stalk y)).map
            (canonicalLocalInverseTraceSections f M L τ y)) ≫
        canonicalAffineSectionsEvaluation b ((Scheme.Modules.pullback a).obj M) := by
  let j := Y.fromSpecStalk y
  let a := Limits.pullback.fst f j
  let b := Limits.pullback.snd f j
  let N := (Scheme.Modules.pullback a).obj M
  let P := (Scheme.Modules.pullback j).obj L
  let Q := (pushforward b).obj N
  let T := tilde.functor (Y.presheaf.stalk y)
  let e := canonicalLocalSpectrumCoefficientIso Y y L
  let r := canonicalLocalInverseTraceSections f M L τ y
  let t : P ⟶ Q := (Scheme.Modules.pullback j).map (inv τ) ≫
    (cartesianBaseChangeMap a b f j (IsPullback.of_hasPullback f j)).app M
  have hr : (stalkFromSpecStalkSectionsIso Y y L).hom ≫ moduleSpecΓFunctor.map t = r :=
    canonicalLocalInverseTraceSections_normalization f M L τ y
  have hn : T.map (moduleSpecΓFunctor.map t) ≫ Q.fromTildeΓ = P.fromTildeΓ ≫ t :=
    fromTildeΓNatTrans.naturality t
  have he : e.hom ≫ t = T.map r ≫ Q.fromTildeΓ := by
    change (T.map (stalkFromSpecStalkSectionsIso Y y L).hom ≫ P.fromTildeΓ) ≫ t = _
    rw [Category.assoc, ← hn, ← Category.assoc, ← T.map_comp, hr]
  have ht : t = e.inv ≫ T.map r ≫ Q.fromTildeΓ := by
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using
      congrArg (fun z => e.inv ≫ z) he
  have h := ordinaryTracePullback_baseChange a b f j (IsPullback.of_hasPullback f j) τ
  change (Scheme.Modules.pullback a).map (ordinaryTracePullback f τ) =
    (ordinaryTracePullbackSquareIso a b f j (IsPullback.of_hasPullback f j)).hom.app L ≫
      (Scheme.Modules.pullback b).map t ≫ (pullbackPushforwardAdjunction b).counit.app N at h
  simpa only [ht, Functor.map_comp, canonicalAffineSectionsEvaluation, Category.assoc] using h

end AlgebraicGeometry.Scheme.Cohomology
