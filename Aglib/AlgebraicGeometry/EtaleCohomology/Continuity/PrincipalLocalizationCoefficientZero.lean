/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Continuity.PrincipalLocalizationZero
public import Aglib.AlgebraicGeometry.Spec.PrincipalFractionProjection

/-! # Principal-localization zero for arbitrary original coefficients

The existing principal scheme diagram and the complete original pullback
cohomology cocone are reused without changing their maps. The coefficients
are an arbitrary abelian sheaf on the original qcqs source, not necessarily
constant, finite, or constructible. The Ext universe remains independent.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open IsLocalization.PrincipalDiagram
open AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit
open scoped nonZeroDivisors

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.PrincipalLocalization

universe u e

attribute [local instance] hasSheafifyLarge

open Stalk ConstantFinite.PrincipalLocalization

section Localization

variable {R : Type u} [CommRing R] (M : Submonoid R)
  (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of R))
  [CompactSpace X] [QuasiSeparatedSpace X]
  [hExt : ∀ s : Finset M, HasExt.{e} (AbelianSheaf.{u, u + 1}
    ((PrincipalNeighborhoodLimit.baseChangeDiagram M p).obj (op s)))]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback p (Spec.algebraMap R S)))]
  [HasColimitsOfShape (Finset M) AddCommGrpCat.{e}] [UnivLE.{u, e}]

local instance : IsConnected (Finset M) := IsFiltered.isConnected _

local instance (s : Finset M) : CompactSpace ((coefficientDiagram M p).obj s).unop :=
  baseChange_stage_compact M p (op s)

local instance (s : Finset M) : QuasiSeparatedSpace ((coefficientDiagram M p).obj s).unop :=
  baseChange_stage_quasiSeparated M p (op s)

local instance (s : Finset M) :
    HasExt.{e} (AbelianSheaf.{u, u + 1} ((coefficientDiagram M p).obj s).unop) := hExt s

local instance (s : Finset M) :
    HasExt.{e} (AbelianSheaf.{u, u + 1} ((schemeDiagram M p).obj (op s)).left) := hExt s

local instance : HasExt.{e} (AbelianSheaf.{u, u + 1}
    (coefficientLimitCocone M S p).pt.unop) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback p (Spec.algebraMap R S))))

local instance : HasExt.{e} (AbelianSheaf.{u, u + 1}
    (coefficientBaseCone M p).pt.unop) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} X))

local instance {s t : Finset M} (a : s ⟶ t) :
    IsAffineHom ((coefficientDiagram M p).map a).unop :=
  baseChange_transition_affine M p a.op

/-- The same original class, with arbitrary coefficients, becomes zero at an
actual principal stage if its original localization pullback is zero. -/
theorem exists_principalStage_cohomologyPullback_eq_zero
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (c : Sheaf.H.{e} F q)
    (hc : cohomologyPullback.{u, e, e}
      (pullback.fst p (Spec.algebraMap R S)) F q c = 0) :
    ∃ s : Finset M,
      cohomologyPullback.{u, e, e} ((schemeDiagram M p).obj (op s)).hom F q c = 0 := by
  let D := coefficientDiagram M p
  let b := coefficientBaseCone M p
  let k := coefficientLimitCocone M S p
  let l : b.pt ⟶ k.pt := (pullback.fst p (Spec.algebraMap R S)).op
  have hk : IsColimit k :=
    (baseChangeConeIsLimit M S p).op.whiskerEquivalence (opOpEquivalence (Finset M)).symm
  have hl : ∀ s, b.π.app s ≫ k.ι.app s = l := fun s =>
    congrArg Quiver.Hom.op (baseChangeProjection_base M S p (op s))
  let : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget AddCommGrpCat.{e}) :=
    preservesFilteredColimitsOfSize_of_univLE.{e, e, u, u} _
  exact exists_pullback_eq_zero_of_colimit D b k l hl F q
    (isColimitPullbackCohomologyCocone D b k hk l hl F q) c hc

variable [hExtOpen : ∀ s : Finset M,
  HasExt.{e} (AbelianSheaf.{u, u + 1} (stageSourceOpen M p s))]

/-- The zero is on the literal inverse-image open in the unchanged source,
with the original inverse-image coefficient rather than a chosen equivalent model. -/
theorem exists_principalOpen_cohomologyPullback_eq_zero
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (c : Sheaf.H.{e} F q)
    (hc : cohomologyPullback.{u, e, e}
      (pullback.fst p (Spec.algebraMap R S)) F q c = 0) :
    ∃ s : Finset M,
      cohomologyPullback.{u, e, e} (stageSourceOpen M p s).ι F q c = 0 := by
  obtain ⟨s, hs⟩ := exists_principalStage_cohomologyPullback_eq_zero M S p F q c hc
  let i := stageOpenIso M p s
  have hi : i.inv ≫ ((schemeDiagram M p).obj (op s)).hom = (stageSourceOpen M p s).ι := by
    rw [← stageOpenIso_hom_over, i.inv_hom_id_assoc]
  have h := cohomologyPullback_comp.{u, e, e, e}
    ((schemeDiagram M p).obj (op s)).hom i.inv F q c
  rw [hs, map_zero] at h
  have hz : cohomologyPullback.{u, e, e}
      (i.inv ≫ ((schemeDiagram M p).obj (op s)).hom) F q c = 0 :=
    (cohomologyMapIso_bijective
      ((inverseImageComp ((schemeDiagram M p).obj (op s)).hom i.inv).app F) q).injective
        (h.trans (map_zero _).symm)
  rw [hi] at hz
  exact ⟨s, hz⟩

end Localization

section FractionField

variable (R K : Type u) [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of R)) [CompactSpace X] [QuasiSeparatedSpace X]
  [∀ s : Finset R⁰, HasExt.{e} (AbelianSheaf.{u, u + 1}
    ((PrincipalNeighborhoodLimit.baseChangeDiagram R⁰ p).obj (op s)))]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback p (Spec.algebraMap R K)))]
  [∀ s : Finset R⁰, HasExt.{e} (AbelianSheaf.{u, u + 1} (stageSourceOpen R⁰ p s))]
  [HasColimitsOfShape (Finset R⁰) AddCommGrpCat.{e}] [UnivLE.{u, e}]

/-- Generic zero spreads to a nonzero principal stage of the original base;
the same original class vanishes on its literal inverse-image open. -/
theorem exists_fraction_principalOpen_cohomologyPullback_eq_zero
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (c : Sheaf.H.{e} F q)
    (hc : cohomologyPullback.{u, e, e}
      (pullback.fst p (Spec.algebraMap R K)) F q c = 0) :
    ∃ s : Finset R⁰, denominator R⁰ s ≠ 0 ∧ Nonempty (stageBaseOpen R⁰ s) ∧
      cohomologyPullback.{u, e, e} (stageSourceOpen R⁰ p s).ι F q c = 0 := by
  obtain ⟨s, hs⟩ := exists_principalOpen_cohomologyPullback_eq_zero R⁰ K p F q c hc
  refine ⟨s, nonZeroDivisors.ne_zero (denominator_mem R⁰ s), ?_, hs⟩
  let x : Spec (.of (stage R⁰ s)) := Classical.choice inferInstance
  exact ⟨⟨(Spec.algebraMap R (stage R⁰ s)) x, ⟨x, rfl⟩⟩⟩

end FractionField

end AlgebraicGeometry.Scheme.EtaleCohomology.Continuity.PrincipalLocalization
