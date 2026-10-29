/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Algebra.Homology.DerivedCategory.Ext.ChangeUniverseExact
public import Aglib.AlgebraicGeometry.EtaleCohomology.SmoothBaseChange.CurveFieldInvarianceConstantModules

/-! # Original curve H1 comparisons in independent Ext universes

The actual exact-functor/source-precomposition comparison commutes with native
universe change. Its proved square transports the original pullback, before
applying the actual coefficient and module transports. No colimit-size guard
is left on the original bounded literal constant-module statement.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.Modules

namespace AlgebraicGeometry.Scheme.EtaleCohomology.SmoothBaseChange

universe u r eX eY

attribute [local instance] hasSheafifyLarge HasExt.standard ModuleCat.Sheaf.hasSheafify
  ModuleCat.Sheaf.cohomologyModule

variable (k K : Type u) [Field k] [Field K] [IsSepClosed k] [IsSepClosed K] [Algebra k K]
    {U : Scheme.{u}} [IsAffine U] [ConnectedSpace U]
    (p : U ⟶ Spec (.of k)) [SmoothOfRelativeDimension 1 p]
    [HasExt.{eX} (AbelianSheaf.{u, u + 1} U)]
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} (pullback p (Spec.algebraMap k K)))]

/-- Original H1 pullback for bounded constant abelian values, with independent
original source and target Ext universes and no auxiliary colimit-size premise. -/
theorem smoothAffineCurve_constantAbelianH1_raw_bijective_arbitraryExt
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k))
    (A : AddCommGrpCat.{u + 1}) (hA : ∀ a : A, n • a = 0) :
    Function.Bijective (cohomologyPullback.{u, eX, eY}
      (pullback.fst p (Spec.algebraMap k K))
      ((constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A) 1) := by
  let f := pullback.fst p (Spec.algebraMap k K)
  let s := etaleAdditiveCoefficientAction f
  let L := (constantSheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}).obj A
  have hstandard : Function.Bijective (cohomologyPullback.{u, u + 2, u + 2} f L 1) :=
    smoothAffineCurve_constantAbelianH1_raw_bijective k K p n hn hunit A hA
  have hs : Function.Bijective
      (Topos.AdditiveCoefficientAction.cohomologyMap.{u + 1, u, u + 1, u, u + 1,
        u + 2, u + 2} s L 1) := by
    rw [← cohomologyPullback_eq_additiveToposMap]
    exact hstandard
  rw [cohomologyPullback_eq_additiveToposMap]
  exact Topos.AdditiveCoefficientAction.cohomologyMap_bijective_changeUniverse.{u + 1, u,
    u + 1, u, u + 1, u + 2, u + 2, eX, eY} s L 1 hs

/-- The original scalar-linear pullback for any bounded literal constant
module is bijective, with independent ring and both Ext universes. -/
theorem smoothAffineCurve_constantModuleH1_raw_bijective_arbitraryExt
    (R : Type r) [CommRing R] (M : ModuleCat.{u + 1} R)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hM : ∀ x : M, n • x = 0) :
    Function.Bijective (moduleCohomologyPullback.{u, r, eX, eY} R
      (pullback.fst p (Spec.algebraMap k K))
      ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) 1) := by
  let f := pullback.fst p (Spec.algebraMap k K)
  let F := (constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M
  have hraw : Function.Bijective (cohomologyPullback.{u, eX, eY} f
      ((moduleUnderlying R U).obj F) 1) :=
    cohomologyPullback_bijective_of_iso f ((moduleConstantUnderlyingIso R U).app M).symm 1
      (smoothAffineCurve_constantAbelianH1_raw_bijective_arbitraryExt k K p n hn hunit
        ((forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}).obj M) hM)
  exact (cohomologyMapIso_bijective ((moduleInverseImageUnderlyingIso R f).app F).symm 1).comp hraw

/-- The actual constant-module coefficient transport retains bijectivity of
the same original H1 map, without finiteness or Noetherian restrictions. -/
theorem smoothAffineCurve_constantModuleH1_bijective_arbitraryExt
    (R : Type r) [CommRing R] (M : ModuleCat.{u + 1} R)
    (n : ℕ) (hn : 0 < n) (hunit : IsUnit (n : k)) (hM : ∀ x : M, n • x = 0) :
    Function.Bijective (fun x =>
      (ModuleCat.Sheaf.cohomology.{u + 1, u, r, eY}
        (pullback p (Spec.algebraMap k K)).smallEtaleTopology R 1).map
          ((moduleInverseImageConstantIso R (pullback.fst p (Spec.algebraMap k K))).hom.app M)
        (moduleCohomologyPullback.{u, r, eX, eY} R
          (pullback.fst p (Spec.algebraMap k K))
          ((constantSheaf U.smallEtaleTopology (ModuleCat.{u + 1} R)).obj M) 1 x)) := by
  let E := (ModuleCat.Sheaf.cohomology.{u + 1, u, r, eY}
      (pullback p (Spec.algebraMap k K)).smallEtaleTopology R 1).mapIso
        ((moduleInverseImageConstantIso R (pullback.fst p (Spec.algebraMap k K))).app M)
  exact E.toLinearEquiv.bijective.comp
    (smoothAffineCurve_constantModuleH1_raw_bijective_arbitraryExt k K p R M n hn hunit hM)

end AlgebraicGeometry.Scheme.EtaleCohomology.SmoothBaseChange
