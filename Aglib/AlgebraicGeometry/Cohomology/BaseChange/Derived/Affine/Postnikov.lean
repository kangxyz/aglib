/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Derived.Affine
public import Aglib.AlgebraicGeometry.Cohomology.BaseChange.Derived.Shift
public import Aglib.Algebra.Homology.DerivedCategory.Plus.Postnikov.Comparison
public import Aglib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus.TStructure

/-!
# Original derived affine flat base change on bounded-below quasicoherent homology

The single-object theorem and original shift-compatible transformation feed
the shared native Postnikov comparison. Only quasicoherence of the original
homology objects is assumed. No termwise quasicoherence, upper bound,
cohomological-dimension bound or convergence premise is introduced.
-/

@[expose] public section

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

/-- Retain the original installed standard derived models. -/
local instance affinePostnikovBaseChangeStandard (Z : Scheme.{u}) :
    HasDerivedCategory.{u + 1} Z.Modules := HasDerivedCategory.standard _

variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}
  (a : Y ⟶ X) (b : Y ⟶ Spec S) (f : X ⟶ Spec R) [QuasiCompact f] [QuasiSeparated f]
  (φ : R ⟶ S) (h : IsPullback a b f (Spec.map φ)) (hflat : φ.hom.Flat)

/-- The original affine derived base-change map is invertible on a quasicoherent single
in every integer degree, by its original native shift compatibility. -/
theorem derivedFlatBaseChangeMap_isIso_single_degree_of_spec
    (M : X.Modules) [M.IsQuasicoherent] (i : ℤ) :
    letI : Flat (Spec.map φ) := Flat.SpecMap_iff.mpr hflat
    IsIso ((derivedFlatBaseChangeMap a b f (Spec.map φ) h).app
      ((DerivedCategory.Plus.singleFunctor X.Modules i).obj M)) := by
  let : Flat (Spec.map φ) := Flat.SpecMap_iff.mpr hflat
  let := flat_cartesian_baseChange a b f (Spec.map φ) h
  let τ := derivedFlatBaseChangeMap a b f (Spec.map φ) h
  let K := (DerivedCategory.Plus.singleFunctor X.Modules 0).obj M
  let : IsIso (τ.app K) := derivedFlatBaseChangeMap_isIso_single_of_spec a b f φ h hflat M
  have hs : IsIso (τ.app (K⟦-i⟧)) := by
    rw [τ.app_shift (-i) K]
    infer_instance
  let e : K⟦-i⟧ ≅ (DerivedCategory.Plus.singleFunctor X.Modules i).obj M :=
    ((DerivedCategory.Plus.singleFunctors X.Modules).shiftIso (-i) i 0 (by omega)).app M
  exact (NatTrans.isIso_app_iff_of_iso τ e).mp hs

/-- The existing original derived flat base-change map is invertible over affine bases
on every bounded-below object whose original homology sheaves are quasicoherent. -/
theorem derivedFlatBaseChangeMap_isIso_of_spec
    (K : DerivedCategory.Plus X.Modules)
    (hK : ∀ i : ℤ, ((DerivedCategory.Plus.homologyFunctor X.Modules i).obj K).IsQuasicoherent) :
    letI : Flat (Spec.map φ) := Flat.SpecMap_iff.mpr hflat
    IsIso ((derivedFlatBaseChangeMap a b f (Spec.map φ) h).app K) := by
  let : Flat (Spec.map φ) := Flat.SpecMap_iff.mpr hflat
  let := flat_cartesian_baseChange a b f (Spec.map φ) h
  let τ := derivedFlatBaseChangeMap a b f (Spec.map φ) h
  apply DerivedCategory.Plus.isIso_app_of_homology_singles τ
    (fun L n hL => by
      let : L.IsGE n := hL
      let : ((derivedPushforwardPlus f).obj L).IsGE n :=
        (pushforward f).rightDerivedFunctorPlus_isGE L n
      exact (pullback (Spec.map φ)).rightDerivedFunctorPlus_isGE
        ((derivedPushforwardPlus f).obj L) n)
    (fun L n hL => by
      let : L.IsGE n := hL
      let : ((derivedFlatPullbackPlus a).obj L).IsGE n :=
        (pullback a).rightDerivedFunctorPlus_isGE L n
      exact (pushforward b).rightDerivedFunctorPlus_isGE ((derivedFlatPullbackPlus a).obj L) n) K
  intro i
  let : ((DerivedCategory.Plus.homologyFunctor X.Modules i).obj K).IsQuasicoherent := hK i
  exact derivedFlatBaseChangeMap_isIso_single_degree_of_spec a b f φ h hflat _ i

end AlgebraicGeometry.Scheme.Modules
