/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Modules.BaseChange.Affine.Mate
public import Aglib.Algebra.Category.ModuleCat.ChangeOfRings.BaseChange
public import Aglib.AlgebraicGeometry.Modules.QuasiCoherent.Affine.PullbackSections
public import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Affine sections of the original base-change mate

The comparisons use the native tilde/global-section equivalence and its original
adjunction unit. The scalar map is compared with the actual geometric mate.
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.Scheme.Modules

/-- Global sections reflect isomorphisms between affine quasicoherent module sheaves. -/
theorem isIso_of_globalSections_isIso {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (f : M ⟶ N) [IsIso (moduleSpecΓFunctor.map f)] : IsIso f := by
  have hn := fromTildeΓNatTrans.naturality f
  change (tilde.functor R).map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
    M.fromTildeΓ ≫ f at hn
  have : IsIso (M.fromTildeΓ ≫ f) := by
    rw [← hn]
    infer_instance
  exact IsIso.of_isIso_comp_left M.fromTildeΓ f

/-- The affine pullback comparison sends the unit tensor to the actual geometric unit. -/
theorem affinePullbackGlobalSectionsIso_one_tmul {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (M : (Spec R).Modules) [M.IsQuasicoherent] (m : moduleSpecΓFunctor.obj M) :
    (affinePullbackGlobalSectionsIso φ M).hom ((1 : S) ⊗ₜ[R,φ.hom] m) =
      (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app M).app ⊤) m := by
  exact congrArg (fun q => q m) (affinePullbackGlobalSectionsIso_unit φ M)

variable {R S T P : CommRingCat.{u}}
  (i : R ⟶ S) (j : R ⟶ T) (k : S ⟶ P) (l : T ⟶ P)

/-- The actual geometric mate on affine sections, through the native scalar comparisons. -/
def specBaseChangeSectionsMap
    (h : IsPullback (Spec.map k) (Spec.map l) (Spec.map i) (Spec.map j))
    (M : (Spec S).Modules) [M.IsQuasicoherent] :
    (ModuleCat.extendScalars j.hom).obj
        ((ModuleCat.restrictScalars i.hom).obj (moduleSpecΓFunctor.obj M)) ⟶
      (ModuleCat.restrictScalars l.hom).obj
        ((ModuleCat.extendScalars k.hom).obj (moduleSpecΓFunctor.obj M)) := by
  letI := isQuasicoherent_pushforward i M
  exact (ModuleCat.extendScalars j.hom).map ((pushforwardGlobalSectionsIso i).inv.app M) ≫
    (affinePullbackGlobalSectionsIso j ((pushforward (Spec.map i)).obj M)).hom ≫
    moduleSpecΓFunctor.map
      ((cartesianBaseChangeMap (Spec.map k) (Spec.map l) (Spec.map i) (Spec.map j) h).app M) ≫
    (pushforwardGlobalSectionsIso l).hom.app ((pullback (Spec.map k)).obj M) ≫
    (ModuleCat.restrictScalars l.hom).map (affinePullbackGlobalSectionsIso k M).inv

set_option maxRecDepth 2000 in
/-- The actual affine geometric mate becomes the canonical scalar base-change map. -/
theorem specBaseChangeSectionsMap_eq_scalarBaseChangeMap
    (h : IsPushout i j k l) (M : (Spec S).Modules) [M.IsQuasicoherent] :
    specBaseChangeSectionsMap i j k l (isPullback_SpecMap_of_isPushout i j k l h) M =
      ModuleCat.scalarBaseChangeMap i j k l h.w (moduleSpecΓFunctor.obj M) := by
  let := isQuasicoherent_pushforward i M
  apply ((ModuleCat.extendRestrictScalarsAdj j.hom).homEquiv _ _).injective
  ext m
  rw [ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
    ModuleCat.extendRestrictScalarsAdj_homEquiv_apply,
    ModuleCat.scalarBaseChangeMap_one_tmul]
  apply (ConcreteCategory.bijective_of_isIso (affinePullbackGlobalSectionsIso k M).hom).injective
  change (affinePullbackGlobalSectionsIso k M).hom
      ((affinePullbackGlobalSectionsIso k M).inv
        ((((cartesianBaseChangeMap (Spec.map k) (Spec.map l) (Spec.map i) (Spec.map j)
          (isPullback_SpecMap_of_isPushout i j k l h)).app M).app ⊤)
            ((affinePullbackGlobalSectionsIso j ((pushforward (Spec.map i)).obj M)).hom
              ((1 : T) ⊗ₜ[R,j.hom] m)))) =
    (affinePullbackGlobalSectionsIso k M).hom ((1 : P) ⊗ₜ[S,k.hom] m)
  simp only [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ModuleCat.id_apply]
  rw [affinePullbackGlobalSectionsIso_one_tmul, affinePullbackGlobalSectionsIso_one_tmul]
  have hu := congrArg (fun q => (q.app ⊤) m)
    (cartesianBaseChangeMap_unit (Spec.map k) (Spec.map l) (Spec.map i) (Spec.map j)
      (isPullback_SpecMap_of_isPushout i j k l h) M)
  simpa [cartesianPushforwardSquare] using hu.symm

set_option maxRecDepth 2000 in
/-- Canonical module base change on an affine spectrum pushout, for arbitrary
quasicoherent coefficients and arbitrary ring homomorphisms. -/
theorem cartesianBaseChangeMap_isIso_spec (h : IsPushout i j k l)
    (M : (Spec S).Modules) [M.IsQuasicoherent] :
    IsIso ((cartesianBaseChangeMap (Spec.map k) (Spec.map l) (Spec.map i) (Spec.map j)
      (isPullback_SpecMap_of_isPushout i j k l h)).app M) := by
  let := isQuasicoherent_pushforward i M
  let := isQuasicoherent_pullback k M
  have : ((pushforward (Spec.map i) ⋙ pullback (Spec.map j)).obj M).IsQuasicoherent :=
    isQuasicoherent_pullback j ((pushforward (Spec.map i)).obj M)
  have : ((pullback (Spec.map k) ⋙ pushforward (Spec.map l)).obj M).IsQuasicoherent :=
    isQuasicoherent_pushforward l ((pullback (Spec.map k)).obj M)
  let α := (cartesianBaseChangeMap (Spec.map k) (Spec.map l) (Spec.map i) (Spec.map j)
    (isPullback_SpecMap_of_isPushout i j k l h)).app M
  let a := (ModuleCat.extendScalars j.hom).map ((pushforwardGlobalSectionsIso i).inv.app M) ≫
    (affinePullbackGlobalSectionsIso j ((pushforward (Spec.map i)).obj M)).hom
  let b := (pushforwardGlobalSectionsIso l).hom.app ((pullback (Spec.map k)).obj M) ≫
    (ModuleCat.restrictScalars l.hom).map (affinePullbackGlobalSectionsIso k M).inv
  have hs : IsIso (a ≫ moduleSpecΓFunctor.map α ≫ b) := by
    change IsIso (specBaseChangeSectionsMap i j k l
      (isPullback_SpecMap_of_isPushout i j k l h) M)
    rw [specBaseChangeSectionsMap_eq_scalarBaseChangeMap i j k l h M]
    exact ModuleCat.scalarBaseChangeMap_isIso_of_isPushout i j k l h
      (moduleSpecΓFunctor.obj M)
  have : IsIso (moduleSpecΓFunctor.map α ≫ b) := IsIso.of_isIso_comp_left a _
  have : IsIso (moduleSpecΓFunctor.map α) := IsIso.of_isIso_comp_right _ b
  exact isIso_of_globalSections_isIso α

end AlgebraicGeometry.Scheme.Modules
