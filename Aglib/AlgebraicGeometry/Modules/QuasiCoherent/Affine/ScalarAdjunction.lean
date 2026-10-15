/-
Copyright (c) 2026 Quillen K-theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.Pullback
/-! # Compatibility of the affine scalar adjunction comparisons

The existing tilde pullback and pushforward comparisons preserve the original geometric
and scalar adjunction units. Global sections detect equality of maps out of a
quasicoherent sheaf on an affine spectrum.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory AlgebraicGeometry
namespace AlgebraicGeometry.Scheme.Modules
variable {R S : CommRingCat.{u}} (φ : R ⟶ S)
/-- Global sections of the actual associated-sheaf pushforward comparison. -/
theorem tildePushforwardIso_globalSections (N : ModuleCat S) :
    moduleSpecΓFunctor.map ((tildePushforwardIso φ).hom.app N) =
      (tilde.adjunction (R := R)).unit.app
          (moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde N))) ≫
        moduleSpecΓFunctor.map ((tilde.functor R).map
          ((pushforwardGlobalSectionsIso φ).hom.app (tilde N) ≫
            (ModuleCat.restrictScalars φ.hom).map (tilde.toTildeΓNatIso.inv.app N))) := by
  have hc := (tilde.adjunction (R := R)).right_triangle_components
    ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde N))
  have : ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde N)).IsQuasicoherent :=
    isQuasicoherent_pushforward φ (tilde N)
  have he : inv (moduleSpecΓFunctor.map
        ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde N)).fromTildeΓ) =
      (tilde.adjunction (R := R)).unit.app
        (moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde N))) := by
    apply (cancel_mono (moduleSpecΓFunctor.map
      ((Scheme.Modules.pushforward (Spec.map φ)).obj (tilde N)).fromTildeΓ)).mp
    rw [IsIso.inv_hom_id]
    exact hc.symm
  simpa [tildePushforwardIso, Functor.map_comp, Category.assoc] using
    congrArg (fun q => q ≫ moduleSpecΓFunctor.map ((tilde.functor R).map
      ((pushforwardGlobalSectionsIso φ).hom.app (tilde N) ≫
        (ModuleCat.restrictScalars φ.hom).map (tilde.toTildeΓNatIso.inv.app N)))) he
/-- The global-sections comparison retains the original tilde adjunction unit. -/
theorem tildePushforwardIso_globalSections_unit (N : ModuleCat S) :
    moduleSpecΓFunctor.map ((tildePushforwardIso φ).hom.app N) =
      (pushforwardGlobalSectionsIso φ).hom.app (tilde N) ≫
        (ModuleCat.restrictScalars φ.hom).map (tilde.toTildeΓNatIso.inv.app N) ≫
        (tilde.adjunction (R := R)).unit.app ((ModuleCat.restrictScalars φ.hom).obj N) := by
  rw [tildePushforwardIso_globalSections]
  exact ((tilde.adjunction (R := R)).unit.naturality
    ((pushforwardGlobalSectionsIso φ).hom.app (tilde N) ≫
      (ModuleCat.restrictScalars φ.hom).map (tilde.toTildeΓNatIso.inv.app N))).symm
/-- Global sections detect equality of morphisms out of an affine quasicoherent sheaf. -/
theorem hom_eq_of_globalSections_eq {M N : (Spec R).Modules} [M.IsQuasicoherent]
    (f g : M ⟶ N) (h : moduleSpecΓFunctor.map f = moduleSpecΓFunctor.map g) : f = g := by
  apply (cancel_epi M.fromTildeΓ).mp
  have hf := Scheme.Modules.fromTildeΓNatTrans.naturality f
  have hg := Scheme.Modules.fromTildeΓNatTrans.naturality g
  change (tilde.functor R).map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
    M.fromTildeΓ ≫ f at hf
  change (tilde.functor R).map (moduleSpecΓFunctor.map g) ≫ N.fromTildeΓ =
    M.fromTildeΓ ≫ g at hg
  rw [← hf, ← hg, h]
/-- The affine pullback comparison retains the original composed-adjunction unit. -/
theorem tildePullbackIso_globalSections_unit (M : ModuleCat R) :
    (tilde.adjunction (R := R)).unit.app M ≫
      moduleSpecΓFunctor.map
        ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)) ≫
      (pushforwardGlobalSectionsIso φ).hom.app
        ((Scheme.Modules.pullback (Spec.map φ)).obj (tilde M)) ≫
      (ModuleCat.restrictScalars φ.hom).map
        (moduleSpecΓFunctor.map ((tildePullbackIso φ).hom.app M)) =
    (ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M ≫
      (ModuleCat.restrictScalars φ.hom).map
        ((tilde.adjunction (R := S)).unit.app ((ModuleCat.extendScalars φ.hom).obj M)) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
      (((tilde.adjunction (R := R)).comp
        (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ))).ofNatIsoRight
          (pushforwardGlobalSectionsIso φ))
      ((ModuleCat.extendRestrictScalarsAdj φ.hom).comp (tilde.adjunction (R := S))) M
  have hc := Adjunction.comp_unit_app (ModuleCat.extendRestrictScalarsAdj φ.hom)
    (tilde.adjunction (R := S)) M
  rw [hc] at h
  simpa only [tildePullbackIso, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.comp_unit_app, Functor.comp_map, Functor.comp_obj,
    tilde.functor_obj, Category.assoc] using h
/-- The original affine pullback and pushforward comparisons preserve the geometric unit. -/
theorem tildePullbackIso_unit (M : ModuleCat R) :
    (Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M) ≫
      (Scheme.Modules.pushforward (Spec.map φ)).map ((tildePullbackIso φ).hom.app M) ≫
      (tildePushforwardIso φ).hom.app ((ModuleCat.extendScalars φ.hom).obj M) =
    (tilde.functor R).map ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M) := by
  apply ((tilde.adjunction (R := R)).homEquiv _ _).injective
  change (tilde.adjunction (R := R)).unit.app M ≫ moduleSpecΓFunctor.map
      ((Scheme.Modules.pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M) ≫
        (Scheme.Modules.pushforward (Spec.map φ)).map ((tildePullbackIso φ).hom.app M) ≫
          (tildePushforwardIso φ).hom.app ((ModuleCat.extendScalars φ.hom).obj M)) =
    (tilde.adjunction (R := R)).unit.app M ≫ moduleSpecΓFunctor.map
      ((tilde.functor R).map ((ModuleCat.extendRestrictScalarsAdj φ.hom).unit.app M))
  simp only [Functor.map_comp]
  rw [tildePushforwardIso_globalSections]
  erw [← (tilde.adjunction (R := R)).unit.naturality]
  simp only [Functor.id_map]
  erw [← (tilde.adjunction (R := R)).unit.naturality]
  simp only [Functor.id_map, Category.assoc]
  have hn := (pushforwardGlobalSectionsIso φ).hom.naturality
    ((tildePullbackIso φ).hom.app M)
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  have h := congrArg (fun q => q ≫
    (ModuleCat.restrictScalars φ.hom).map
      (tilde.toTildeΓNatIso.inv.app ((ModuleCat.extendScalars φ.hom).obj M)) ≫
    (tilde.adjunction (R := R)).unit.app
      ((ModuleCat.restrictScalars φ.hom).obj ((ModuleCat.extendScalars φ.hom).obj M)))
    (tildePullbackIso_globalSections_unit φ M)
  have hc : (ModuleCat.restrictScalars φ.hom).map
        ((tilde.adjunction (R := S)).unit.app ((ModuleCat.extendScalars φ.hom).obj M)) ≫
      (ModuleCat.restrictScalars φ.hom).map
        (tilde.toTildeΓNatIso.inv.app ((ModuleCat.extendScalars φ.hom).obj M)) = 𝟙 _ := by
    rw [← Functor.map_comp]
    change (ModuleCat.restrictScalars φ.hom).map
      (tilde.toTildeΓNatIso.hom.app _ ≫ tilde.toTildeΓNatIso.inv.app _) = _
    simp
  simp only [Category.assoc] at h
  rw [reassoc_of% hc] at h
  simpa only [Functor.comp_obj, Functor.id_obj, tilde.functor_obj] using h
end AlgebraicGeometry.Scheme.Modules
