/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PullbackConstantDescent
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.RelativePullbackCoefficient
public import Aglib.AlgebraicGeometry.Spec.PrincipalBaseChangeLimit

/-! # Original constant-class zero at a principal localization stage

This is a specialization of existing qcqs constant-zero continuity to the
original principal-localization diagram. The coefficient and restriction maps
are unchanged, and the Ext universe remains independent.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open IsLocalization.PrincipalDiagram
open AlgebraicGeometry.Scheme.PrincipalNeighborhoodLimit

namespace AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite.PrincipalLocalization

universe u e

attribute [local instance] hasSheafifyLarge

open Stalk Curves

variable {R : Type u} [CommRing R] (M : Submonoid R)
  (S : Type u) [CommRing S] [Algebra R S] [IsLocalization M S]
  {X : Scheme.{u}} (p : X ⟶ Spec (.of R))

/-- The original principal diagram in cohomological direction. -/
def coefficientDiagram : Finset M ⥤ Scheme.{u}ᵒᵖ :=
  (opOpEquivalence (Finset M)).inverse ⋙
    (PrincipalNeighborhoodLimit.baseChangeDiagram M p).op

/-- The original stage maps to the unchanged source. -/
def coefficientBaseCone : Cone (coefficientDiagram M p) :=
  (relativeCoefficientBaseCone (schemeDiagram M p)).whisker
    (opOpEquivalence (Finset M)).inverse

/-- The literal original localization pullback remains the apex. -/
def coefficientLimitCocone : Cocone (coefficientDiagram M p) :=
  (PrincipalNeighborhoodLimit.baseChangeCone M S p).op.whisker
    (opOpEquivalence (Finset M)).inverse

private def coefficientLimitIsColimit : IsColimit (coefficientLimitCocone M S p) :=
  (baseChangeConeIsLimit M S p).op.whiskerEquivalence (opOpEquivalence (Finset M)).symm

private theorem coefficient_cone_composite (s : Finset M) :
    (coefficientBaseCone M p).π.app s ≫ (coefficientLimitCocone M S p).ι.app s =
      (pullback.fst p (Spec.algebraMap R S)).op :=
  congrArg Quiver.Hom.op (baseChangeProjection_base M S p (op s))

variable [CompactSpace X] [QuasiSeparatedSpace X]
  [hExt : ∀ s : Finset M, HasExt.{e} (AbelianSheaf.{u, u + 1}
    ((PrincipalNeighborhoodLimit.baseChangeDiagram M p).obj (op s)))]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} X)]
  [HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback p (Spec.algebraMap R S)))]
  [HasColimitsOfShape (Finset M) AddCommGrpCat.{e}] [UnivLE.{u, e}]

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

/-- A class zero on the original localization is zero at an actual principal stage. -/
theorem exists_principalStage_constantRestriction_eq_zero
    (A : Type u) [AddCommGroup A] (q : ℕ)
    (c : Sheaf.H.{e} (coefficient A X) q)
    (hc : constantRestriction.{u, e, e} A (pullback.fst p (Spec.algebraMap R S)) q c = 0) :
    ∃ s : Finset M,
      constantRestriction.{u, e, e} A ((schemeDiagram M p).obj (op s)).hom q c = 0 :=
  exists_stage_constantCohomologyZero
    (coefficientDiagram M p) (coefficientBaseCone M p)
    (coefficientLimitCocone M S p) (coefficientLimitIsColimit M S p)
    (pullback.fst p (Spec.algebraMap R S)).op (coefficient_cone_composite M S p) A q c hc

variable [hExtOpen : ∀ s : Finset M,
  HasExt.{e} (AbelianSheaf.{u, u + 1} (stageSourceOpen M p s))]

/-- The same zero is on the literal inverse-image open, not a replacement stage. -/
theorem exists_principalOpen_constantRestriction_eq_zero
    (A : Type u) [AddCommGroup A] (q : ℕ)
    (c : Sheaf.H.{e} (coefficient A X) q)
    (hc : constantRestriction.{u, e, e} A (pullback.fst p (Spec.algebraMap R S)) q c = 0) :
    ∃ s : Finset M,
      constantRestriction.{u, e, e} A (stageSourceOpen M p s).ι q c = 0 := by
  obtain ⟨s, hs⟩ := exists_principalStage_constantRestriction_eq_zero M S p A q c hc
  let i := stageOpenIso M p s
  have hi : i.inv ≫ ((schemeDiagram M p).obj (op s)).hom = (stageSourceOpen M p s).ι := by
    rw [← stageOpenIso_hom_over, i.inv_hom_id_assoc]
  have h := constantRestriction_comp.{u, e, e, e} A
    ((schemeDiagram M p).obj (op s)).hom i.inv q c
  rw [hi, hs, map_zero] at h
  exact ⟨s, h⟩

end AlgebraicGeometry.Scheme.EtaleCohomology.ConstantFinite.PrincipalLocalization
