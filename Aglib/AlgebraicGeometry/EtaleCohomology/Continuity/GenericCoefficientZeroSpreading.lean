/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PrincipalLocalizationCoefficientZero

/-! # Generic composite zeros for arbitrary original coefficients

An original class pulled back along an actual cover or other source map is
unchanged. A zero on its generic fibre spreads to a nonzero principal base
open. Original inverse-image composition identifies the coefficients, including
when the source class and the localization system use independent Ext worlds.
The open need not contain a specified closed point.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open IsLocalization.PrincipalDiagram
open AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity

universe u eX e eY

attribute [local instance] hasSheafifyLarge

variable (R K : Type u) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {Z X : Scheme.{u}} [CompactSpace Z] [QuasiSeparatedSpace Z]
  (pZ : Z ⟶ Spec (.of R)) (h : Z ⟶ X)
  [HasExt.{eX} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} Z)]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback pZ (Spec.algebraMap R K)))]
  [∀ s : Finset R⁰, HasExt.{e} (AbelianSheaf.{u, u + 1}
    ((PrincipalNeighborhoodLimit.baseChangeDiagram R⁰ pZ).obj (op s)))]
  [∀ s : Finset R⁰, HasExt.{e} (AbelianSheaf.{u, u + 1} (stageSourceOpen R⁰ pZ s))]
  [HasColimitsOfShape (Finset R⁰) AddCommGrpCat.{e}] [UnivLE.{u, e}]

/-- A zero of the original generic composite spreads to the same original
composite on a nonzero principal base-open inverse image. -/
theorem exists_fraction_principalOpen_composite_zero
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (c : Sheaf.H.{eX} F q)
    (hc : cohomologyPullback.{u, eX, e}
      (pullback.fst pZ (Spec.algebraMap R K) ≫ h) F q c = 0) :
    ∃ s : Finset R⁰, denominator R⁰ s ≠ 0 ∧ Nonempty (stageBaseOpen R⁰ s) ∧
      cohomologyPullback.{u, eX, e} ((stageSourceOpen R⁰ pZ s).ι ≫ h) F q c = 0 := by
  have hcZ : cohomologyPullback.{u, e, e}
      (pullback.fst pZ (Spec.algebraMap R K)) ((inverseImage h).obj F) q
      (cohomologyPullback.{u, eX, e} h F q c) = 0 := by
    have H := cohomologyPullback_comp.{u, eX, e, e}
      h (pullback.fst pZ (Spec.algebraMap R K)) F q c
    rw [hc, map_zero] at H
    exact H.symm
  obtain ⟨s, hs, hne, hz⟩ :=
    PrincipalLocalization.exists_fraction_principalOpen_cohomologyPullback_eq_zero
      R K pZ ((inverseImage h).obj F) q (cohomologyPullback.{u, eX, e} h F q c) hcZ
  refine ⟨s, hs, hne, ?_⟩
  apply (cohomologyMapIso_bijective ((inverseImageComp h (stageSourceOpen R⁰ pZ s).ι).app F)
    q).injective
  exact (cohomologyPullback_comp.{u, eX, e, e}
    h (stageSourceOpen R⁰ pZ s).ι F q c).trans (hz.trans (map_zero _).symm)

/-- An original reconstruction square carries the supplied zero to the same
generic source. Its ensuing principal-open zero retains the original class
and all source maps. In particular this applies to an actual reconstructed cover. -/
theorem exists_fraction_principalOpen_composite_zero_of_reconstruction
    {T Y : Scheme.{u}}
    [HasExt.{e} (AbelianSheaf.{u, u + 1} T)]
    [HasExt.{eY} (AbelianSheaf.{u, u + 1} Y)]
    (a : T ⟶ Z) (b : T ⟶ Spec (.of K))
    (H : IsPullback a b pZ (Spec.algebraMap R K))
    (z : T ⟶ Y) (hY : Y ⟶ X) (hz : z ≫ hY = a ≫ h)
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (c : Sheaf.H.{eX} F q)
    (hc : cohomologyPullback.{u, eX, eY} hY F q c = 0) :
    ∃ s : Finset R⁰, denominator R⁰ s ≠ 0 ∧ Nonempty (stageBaseOpen R⁰ s) ∧
      cohomologyPullback.{u, eX, e} ((stageSourceOpen R⁰ pZ s).ι ≫ h) F q c = 0 := by
  have hT : cohomologyPullback.{u, eX, e} (a ≫ h) F q c = 0 := by
    rw [← hz]
    apply (cohomologyMapIso_bijective ((inverseImageComp hY z).app F) q).injective
    have hcomp := cohomologyPullback_comp.{u, eX, eY, e} hY z F q c
    rw [hc, map_zero] at hcomp
    exact hcomp.trans (map_zero _).symm
  have hgeneric : cohomologyPullback.{u, eX, e}
      (pullback.fst pZ (Spec.algebraMap R K) ≫ h) F q c = 0 := by
    rw [← H.isoPullback_inv_fst, Category.assoc]
    apply (cohomologyMapIso_bijective ((inverseImageComp (a ≫ h) H.isoPullback.inv).app F)
      q).injective
    have hcomp := cohomologyPullback_comp.{u, eX, e, e} (a ≫ h) H.isoPullback.inv F q c
    rw [hT, map_zero] at hcomp
    exact hcomp.trans (map_zero _).symm
  exact exists_fraction_principalOpen_composite_zero R K pZ h F q c hgeneric

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity
