/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PointedNeighborhoodBaseChange
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.RelativeCohomologyTransfer
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartLimitCohomologyCocone
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GeometricCohomologyDiagram
/-! # Original limit cohomology maps from every pointed étale neighborhood -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe u e uI vI uJ vJ
attribute [local instance] hasSheafifyLarge
open Continuity Finite.GeometricNeighborhood

section Reindexed
variable {I : Type uI} [Category.{vI} I] {J : Type uJ} [Category.{vJ} J]
  {X : Scheme.{u}} (D : I ⥤ Over X) (c : Cone D) (K : J ⥤ Iᵒᵖ)
  (F : AbelianSheaf.{u, u + 1} X)
  [hStage : ∀ i, HasExt.{e} (AbelianSheaf.{u, u + 1} (D.obj (K.obj i).unop).left)]
  [hApex : HasExt.{e} (AbelianSheaf.{u, u + 1} c.pt.left)]

local instance reindexedLegStageExt (i : J) : HasExt.{e}
    (AbelianSheaf.{u, u + 1} ((K ⋙ (D ⋙ Over.forget X).op).obj i).unop) := hStage i
local instance reindexedLegApexExt : HasExt.{e}
    (AbelianSheaf.{u, u + 1} ((((Over.forget X).mapCone c).op).whisker K).pt.unop) := hApex

/-- Normalize the entire original leg before substituting a geometric system. -/
theorem relativeReindexedCohomologyLeg_eq (q : ℕ) (i : J) :
    pullbackLimitCohomologyLeg (K ⋙ (D ⋙ Over.forget X).op)
      ((relativeCoefficientBaseCone D).whisker K)
      ((((Over.forget X).mapCone c).op).whisker K) c.pt.hom.op
      (fun i => relativeCoefficient_cone_composite D c (K.obj i)) F q i =
        relativeCohomologyTransfer F q (A := c.pt) (B := D.obj (K.obj i).unop)
          (c.π.app (K.obj i).unop) := rfl
end Reindexed

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsSepClosed Ω]
  {X S : Scheme.{u}} (j : Spec (.of R) ⟶ S) [Etale j] [Mono j]
  (η : Spec (.of Ω) ⟶ S) (hη : Spec.algebraMap R Ω ≫ j = η) (f : X ⟶ S)
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  [HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f))]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

local instance pointedCohomologyStageExt (d : (pointSmallEtale η).fiber.Elements) :
    HasExt.{e} (AbelianSheaf.{u, u + 1}
      ((pointedNeighborhoodBaseChangedDiagram Ω η f).obj d).left) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback d.obj.hom f)))
local instance pointedCohomologyApexExt : HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pointedNeighborhoodBaseChangedCone R Ω j η hη f).pt.left) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f)))
local instance pointedCohomologyChartExt (U : GeometricEtaleNeighborhood R Ω) :
    HasExt.{e} (AbelianSheaf.{u, u + 1}
      ((chartGeometricBaseChangedDiagram R Ω j f).obj (op U)).left) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)).hom f)))

local instance pointedCohomologyRawChartExt (U : GeometricEtaleNeighborhood R Ω) :
    HasExt.{e} (AbelianSheaf.{u, u + 1}
      (pullback (Spec.algebraMap R U.algebra ≫ j) f)) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)).hom f)))

local instance pointedCohomologyReindexedChartExt (U : GeometricEtaleNeighborhood R Ω) :
    HasExt.{e} (AbelianSheaf.{u, u + 1}
      ((chartGeometricBaseChangedDiagram R Ω j f).obj
        ((opOpEquivalence (GeometricEtaleNeighborhood R Ω)).inverse.obj U).unop).left) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R U.algebra ≫ j) f)))

local instance pointedCohomologyChartApexExt : HasExt.{e} (AbelianSheaf.{u, u + 1}
    (chartGeometricBaseChangedCone R Ω j f).pt.left) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f)))

/-- The actual original cohomology map from any marked neighborhood to the limit. -/
def pointedCohomologyLeg (d : (pointSmallEtale η).fiber.Elements) :
    AddCommGrpCat.of (Sheaf.H.{e} ((inverseImage (pullback.snd d.obj.hom f)).obj F) q) ⟶
      AddCommGrpCat.of (Sheaf.H.{e} ((inverseImage
        (pullback.snd (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f)).obj F) q) :=
  relativeCohomologyTransfer F q
    (A := (pointedNeighborhoodBaseChangedCone R Ω j η hη f).pt)
    (B := (pointedNeighborhoodBaseChangedDiagram Ω η f).obj d)
    ((pointedNeighborhoodBaseChangedCone R Ω j η hη f).π.app d)

/-- At a chart neighborhood this is the already proved original limit leg. -/
theorem pointedCohomologyLeg_chart (U : GeometricEtaleNeighborhood R Ω) :
    pointedCohomologyLeg R Ω j η hη f F q
      ((chartToPointElements R Ω j η hη).obj (op U)) =
      (chartLimitCohomologyCocone R Ω j f F q).ι.app U := by
  rw [chartLimitCohomologyCocone_leg]
  exact (congrArg (fun a : (pointedNeighborhoodBaseChangedCone R Ω j η hη f).pt ⟶
      (pointedNeighborhoodBaseChangedDiagram Ω η f).obj
        ((chartToPointElements R Ω j η hη).obj (op U)) =>
      relativeCohomologyTransfer F q
        (A := (pointedNeighborhoodBaseChangedCone R Ω j η hη f).pt)
        (B := (pointedNeighborhoodBaseChangedDiagram Ω η f).obj
          ((chartToPointElements R Ω j η hη).obj (op U))) a)
    (pointedNeighborhoodBaseChangedCone_π_chart R Ω j η hη f (op U))).trans
    (relativeReindexedCohomologyLeg_eq (chartGeometricBaseChangedDiagram R Ω j f)
      (chartGeometricBaseChangedCone R Ω j f)
      (opOpEquivalence (GeometricEtaleNeighborhood R Ω)).inverse F q U).symm

/-- The original map along a pointed refinement equals its native relative transfer. -/
theorem pointedCohomologyRestriction_eq {d d' : (pointSmallEtale η).fiber.Elements}
    (a : d ⟶ d') :
    relativeCohomologyTransfer F q ((pointedNeighborhoodBaseChangedDiagram Ω η f).map a) =
      AddCommGrpCat.ofHom (fibreProductCohomologyRestriction f a.hom F q) :=
  fibreProductCohomologyRestriction_of_heq f a.hom F
    ((pointedNeighborhoodBaseChangedDiagram Ω η f).map a).left rfl _ (HEq.rfl) q

/-- The original limit map is compatible with every actual pointed refinement. -/
theorem pointedCohomologyLeg_restriction {d d' : (pointSmallEtale η).fiber.Elements}
    (a : d ⟶ d') :
    AddCommGrpCat.ofHom (fibreProductCohomologyRestriction f a.hom F q) ≫
        pointedCohomologyLeg R Ω j η hη f F q d =
      pointedCohomologyLeg R Ω j η hη f F q d' := by
  rw [← pointedCohomologyRestriction_eq]
  exact (relativeCohomologyTransfer_comp F q
    (A := (pointedNeighborhoodBaseChangedCone R Ω j η hη f).pt)
    (B := (pointedNeighborhoodBaseChangedDiagram Ω η f).obj d)
    (C := (pointedNeighborhoodBaseChangedDiagram Ω η f).obj d')
    ((pointedNeighborhoodBaseChangedCone R Ω j η hη f).π.app d)
    ((pointedNeighborhoodBaseChangedDiagram Ω η f).map a)).trans
    (congrArg (fun a : (pointedNeighborhoodBaseChangedCone R Ω j η hη f).pt ⟶
        (pointedNeighborhoodBaseChangedDiagram Ω η f).obj d' =>
      relativeCohomologyTransfer F q
        (A := (pointedNeighborhoodBaseChangedCone R Ω j η hη f).pt)
        (B := (pointedNeighborhoodBaseChangedDiagram Ω η f).obj d') a)
      ((pointedNeighborhoodBaseChangedCone R Ω j η hη f).w a))
end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
