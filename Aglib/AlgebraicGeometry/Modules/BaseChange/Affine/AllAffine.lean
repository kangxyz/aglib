/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.BaseChange
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.Mate
public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.PullbackSections
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Pullback

/-! # Canonical base change on arbitrary affine schemes

The original geometric mate is compared with the scalar-adjunction mate on the
pushout of actual global-section rings. The coefficient is arbitrary quasicoherent;
there is no flatness, Noetherianity or finite-generation hypothesis.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

variable {W X T S : Scheme.{u}} [IsAffine W] [IsAffine X] [IsAffine T] [IsAffine S]
  (a : W ⟶ X) (b : W ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
  (h : IsPullback a b f g)

/-- The original geometric mate on actual affine sections, through the native comparisons. -/
def affineBaseChangeSectionsMap (M : X.Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendScalars g.appTop.hom).obj
        ((ModuleCat.restrictScalars f.appTop.hom).obj ((affineΓFunctor X).obj M)) ⟶
      (ModuleCat.restrictScalars b.appTop.hom).obj
        ((ModuleCat.extendScalars a.appTop.hom).obj ((affineΓFunctor X).obj M)) := by
  letI := isQuasicoherent_pushforward_of_isAffine f M
  exact (ModuleCat.extendScalars g.appTop.hom).map
      ((affinePushforwardGlobalSectionsIso f).inv.app M) ≫
    (affinePullbackSectionsIso g ((pushforward f).obj M)).hom ≫
    (affineΓFunctor T).map ((cartesianBaseChangeMap a b f g h).app M) ≫
    (affinePushforwardGlobalSectionsIso b).hom.app ((pullback a).obj M) ≫
    (ModuleCat.restrictScalars b.appTop.hom).map (affinePullbackSectionsIso a M).inv

set_option maxRecDepth 2000 in
/-- The original affine geometric mate becomes the original scalar base-change map. -/
theorem affineBaseChangeSectionsMap_eq_scalarBaseChangeMap
    (M : X.Modules) [M.IsQuasicoherent] :
    affineBaseChangeSectionsMap a b f g h M =
      ModuleCat.scalarBaseChangeMap f.appTop g.appTop a.appTop b.appTop
        (AlgebraicGeometry.isPushout_appTop_of_isPullback h).w ((affineΓFunctor X).obj M) := by
  let := isQuasicoherent_pushforward_of_isAffine f M
  apply ((ModuleCat.extendRestrictScalarsAdj g.appTop.hom).homEquiv _ _).injective
  ext m
  rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
    ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
    ModuleCat.scalarBaseChangeMap_one_tmul]
  apply (ConcreteCategory.bijective_of_isIso (affinePullbackSectionsIso a M).hom).injective
  change (affinePullbackSectionsIso a M).hom
      ((affinePullbackSectionsIso a M).inv
        ((affinePushforwardGlobalSectionsIso b).hom.app ((pullback a).obj M)
          ((affineΓFunctor T).map ((cartesianBaseChangeMap a b f g h).app M)
            ((affinePullbackSectionsIso g ((pushforward f).obj M)).hom
              ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom]
                ((affinePushforwardGlobalSectionsIso f).inv.app M m)))))) =
    (affinePullbackSectionsIso a M).hom
      ((1 : Γ(W, ⊤)) ⊗ₜ[Γ(X, ⊤),a.appTop.hom] m)
  rw [affinePushforwardGlobalSectionsIso_inv_apply,
    affinePushforwardGlobalSectionsIso_hom_apply, affineΓFunctor_map_apply]
  simp only [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]
  rw [affinePullbackSectionsIso_one_tmul, affinePullbackSectionsIso_one_tmul]
  have hu := congrArg (fun q => (q.app ⊤) m) (cartesianBaseChangeMap_unit a b f g h M)
  simpa [cartesianPushforwardSquare] using hu.symm

set_option maxRecDepth 2000 in
/-- The actual cartesian module base-change map is invertible between arbitrary affine schemes. -/
theorem cartesianBaseChangeMap_isIso_of_isAffine (M : X.Modules) [M.IsQuasicoherent] :
    IsIso ((cartesianBaseChangeMap a b f g h).app M) := by
  let := isQuasicoherent_pushforward_of_isAffine f M
  have : ((pushforward f ⋙ pullback g).obj M).IsQuasicoherent :=
    quasicoherent_pullback g ((pushforward f).obj M)
  have : ((pullback a ⋙ pushforward b).obj M).IsQuasicoherent :=
    isQuasicoherent_pushforward_of_isAffine b ((pullback a).obj M)
  let α := (cartesianBaseChangeMap a b f g h).app M
  let c := (ModuleCat.extendScalars g.appTop.hom).map
      ((affinePushforwardGlobalSectionsIso f).inv.app M) ≫
    (affinePullbackSectionsIso g ((pushforward f).obj M)).hom
  let d := (affinePushforwardGlobalSectionsIso b).hom.app ((pullback a).obj M) ≫
    (ModuleCat.restrictScalars b.appTop.hom).map (affinePullbackSectionsIso a M).inv
  have hs : IsIso (c ≫ (affineΓFunctor T).map α ≫ d) := by
    change IsIso (affineBaseChangeSectionsMap a b f g h M)
    rw [affineBaseChangeSectionsMap_eq_scalarBaseChangeMap a b f g h M]
    exact ModuleCat.scalarBaseChangeMap_isIso_of_isPushout f.appTop g.appTop a.appTop b.appTop
      (AlgebraicGeometry.isPushout_appTop_of_isPullback h) ((affineΓFunctor X).obj M)
  have : IsIso ((affineΓFunctor T).map α ≫ d) := IsIso.of_isIso_comp_left c _
  have : IsIso ((affineΓFunctor T).map α) := IsIso.of_isIso_comp_right _ d
  exact isIso_of_affineΓFunctor_map_isIso T α

end AlgebraicGeometry.Scheme.Modules
