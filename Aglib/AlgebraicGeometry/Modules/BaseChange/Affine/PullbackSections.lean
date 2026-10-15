/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.GlobalSections

/-! # Actual pullback sections on arbitrary affine schemes

The comparison is obtained from the original affine tilde adjunction and retains
the original geometric pullback/pushforward unit. No finite-generation hypothesis
is imposed on the quasicoherent coefficient.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)

/-- Actual geometric pullback of native affine tilde is scalar extension. -/
def affineTildePullbackIso :
    affineTildeFunctor Y ⋙ pullback f ≅
      ModuleCat.extendScalars f.appTop.hom ⋙ affineTildeFunctor X :=
  (((affineTildeAdjunction Y).comp (pullbackPushforwardAdjunction f)).ofNatIsoRight
      (affinePushforwardGlobalSectionsIso f)).leftAdjointUniq
    ((ModuleCat.extendRestrictScalarsAdj f.appTop.hom).comp (affineTildeAdjunction X))

/-- The affine tilde comparison preserves the original composed adjunction units. -/
theorem affineTildePullbackIso_globalSections_unit (N : ModuleCat.{u} Γ(Y, ⊤)) :
    (affineTildeAdjunction Y).unit.app N ≫
      (affineΓFunctor Y).map ((pullbackPushforwardAdjunction f).unit.app
        ((affineTildeFunctor Y).obj N)) ≫
      (affinePushforwardGlobalSectionsIso f).hom.app
        ((pullback f).obj ((affineTildeFunctor Y).obj N)) ≫
      (ModuleCat.restrictScalars f.appTop.hom).map
        ((affineΓFunctor X).map ((affineTildePullbackIso f).hom.app N)) =
    (ModuleCat.extendRestrictScalarsAdj f.appTop.hom).unit.app N ≫
      (ModuleCat.restrictScalars f.appTop.hom).map
        ((affineTildeAdjunction X).unit.app
          ((ModuleCat.extendScalars f.appTop.hom).obj N)) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (((affineTildeAdjunction Y).comp (pullbackPushforwardAdjunction f)).ofNatIsoRight
      (affinePushforwardGlobalSectionsIso f))
    ((ModuleCat.extendRestrictScalarsAdj f.appTop.hom).comp (affineTildeAdjunction X)) N
  rw [Adjunction.comp_unit_app] at h
  simpa only [affineTildePullbackIso, Adjunction.ofNatIsoRight_unit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Adjunction.comp_unit_app, Functor.comp_map, Functor.comp_obj,
    Category.assoc] using h

/-- Scalar extension of actual affine sections is the sections of the original pullback. -/
def affinePullbackSectionsIso (M : Y.Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendScalars f.appTop.hom).obj ((affineΓFunctor Y).obj M) ≅
      (affineΓFunctor X).obj ((pullback f).obj M) := by
  letI := affineTildeAdjunction_unit_isIso X
  letI := affineTildeAdjunction_counit_isIso Y M
  exact asIso ((affineTildeAdjunction X).unit.app
      ((ModuleCat.extendScalars f.appTop.hom).obj ((affineΓFunctor Y).obj M))) ≪≫
    (affineΓFunctor X).mapIso
      ((affineTildePullbackIso f).symm.app ((affineΓFunctor Y).obj M) ≪≫
        (pullback f).mapIso (asIso ((affineTildeAdjunction Y).counit.app M)))

/-- The actual affine pullback-section comparison retains the original geometric unit. -/
theorem affinePullbackSectionsIso_unit (M : Y.Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendRestrictScalarsAdj f.appTop.hom).unit.app
        ((affineΓFunctor Y).obj M) ≫
      (ModuleCat.restrictScalars f.appTop.hom).map (affinePullbackSectionsIso f M).hom =
    (affineΓFunctor Y).map ((pullbackPushforwardAdjunction f).unit.app M) ≫
      (affinePushforwardGlobalSectionsIso f).hom.app ((pullback f).obj M) := by
  have h := affineTildePullbackIso_globalSections_unit f ((affineΓFunctor Y).obj M)
  have ht := (affineTildeAdjunction Y).right_triangle_components M
  have hn := (pullbackPushforwardAdjunction f).unit.naturality
    ((affineTildeAdjunction Y).counit.app M)
  have hp := (affinePushforwardGlobalSectionsIso f).hom.naturality
    ((pullback f).map ((affineTildeAdjunction Y).counit.app M))
  have he := congrArg (fun k => k ≫
    (ModuleCat.restrictScalars f.appTop.hom).map
      ((affineΓFunctor X).map
        ((affineTildePullbackIso f).inv.app ((affineΓFunctor Y).obj M))) ≫
    (ModuleCat.restrictScalars f.appTop.hom).map
      ((affineΓFunctor X).map ((pullback f).map
        ((affineTildeAdjunction Y).counit.app M)))) h.symm
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app_assoc] at he
  simp only [Functor.comp_map, Functor.id_map] at hn hp
  erw [← hp] at he
  erw [← Functor.map_comp_assoc, ← hn, Functor.map_comp] at he
  simp only [Functor.map_comp, ← Category.assoc] at he
  change (affineTildeAdjunction Y).unit.app ((affineΓFunctor Y).obj M) ≫
    (affineΓFunctor Y).map ((affineTildeAdjunction Y).counit.app M) = 𝟙 _ at ht
  erw [ht, Category.id_comp] at he
  simpa only [affinePullbackSectionsIso, Iso.trans_hom, Functor.mapIso_hom,
    Iso.app_hom, Iso.symm_hom, asIso_hom, Functor.map_comp, Functor.id_obj,
    Category.assoc] using he

/-- The original affine pullback comparison sends `1 ⊗ m` to the actual geometric unit. -/
theorem affinePullbackSectionsIso_one_tmul (M : Y.Modules) [M.IsQuasicoherent]
    (m : (affineΓFunctor Y).obj M) :
    (affinePullbackSectionsIso f M).hom ((1 : Γ(X, ⊤)) ⊗ₜ[Γ(Y, ⊤),f.appTop.hom] m) =
      (((pullbackPushforwardAdjunction f).unit.app M).app ⊤) m := by
  have h := congrArg (fun q => q m) (affinePullbackSectionsIso_unit f M)
  change (affinePullbackSectionsIso f M).hom
      ((1 : Γ(X, ⊤)) ⊗ₜ[Γ(Y, ⊤),f.appTop.hom] m) =
    (affinePushforwardGlobalSectionsIso f).hom.app ((pullback f).obj M)
      ((affineΓFunctor Y).map ((pullbackPushforwardAdjunction f).unit.app M) m) at h
  rw [affinePushforwardGlobalSectionsIso_hom_apply, affineΓFunctor_map_apply] at h
  exact h

end AlgebraicGeometry.Scheme.Modules
