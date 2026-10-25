/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartPullbackCoefficient
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GeometricCohomologyDiagram
public import Aglib.AlgebraicGeometry.Sites.EtalePointOpenCofinality

/-! # Original cohomology transitions over a chart in an arbitrary base -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe u e
attribute [local instance] hasSheafifyLarge
open Continuity Finite.GeometricNeighborhood

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
  {X S : Scheme.{u}} (j : Spec (.of R) ⟶ S) [Etale j] (f : X ⟶ S)

omit [Etale j] in
/-- The actual strict-local cocone is colimiting in the opposite scheme category. -/
def chartCoefficientLimitIsColimit :
    IsColimit (chartCoefficientLimitCocone R Ω j f) :=
  (chartGeometricBaseChangedConeIsLimit R Ω j f).op.whiskerEquivalence
    (opOpEquivalence (GeometricEtaleNeighborhood R Ω)).symm

/-- The geometric structure arrow is the literal native pullback projection. -/
theorem chartCoefficientStructure_eq (U : GeometricEtaleNeighborhood R Ω) :
    ((chartCoefficientBaseCone R Ω j f).π.app U).unop =
      ((siteBaseChange f).obj
        ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U))).hom := rfl

/-- The geometric transition is the original native base-changed chart morphism. -/
theorem chartCoefficientMap_eq {U V : GeometricEtaleNeighborhood R Ω} (a : U ⟶ V) :
    ((chartCoefficientDiagram R Ω j f).map a).unop =
      ((siteBaseChange f).map
        ((Scheme.EtalePointOpen.postcompose j).map (etaleMap R Ω a))).left := rfl

/-- Compare the complete native triangle before evaluating it at a coefficient sheaf. -/
theorem chartPullbackTriangleIso_eq
    {U V : GeometricEtaleNeighborhood R Ω} (a : U ⟶ V) :
    pullbackTriangleIso ((chartCoefficientBaseCone R Ω j f).π.app V).unop
        ((chartCoefficientBaseCone R Ω j f).π.app U).unop
        ((chartCoefficientDiagram R Ω j f).map a).unop
        (congrArg Quiver.Hom.unop ((chartCoefficientBaseCone R Ω j f).w a)) =
      pullbackTriangleIso ((siteBaseChange f).obj
        ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω V))).hom
        ((siteBaseChange f).obj ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U))).hom
        ((siteBaseChange f).map ((Scheme.EtalePointOpen.postcompose j).map (etaleMap R Ω a))).left
        (MorphismProperty.Over.w ((siteBaseChange f).map
          ((Scheme.EtalePointOpen.postcompose j).map (etaleMap R Ω a)))) := by
  simp only [chartCoefficientStructure_eq, chartCoefficientMap_eq]
  rfl

/-- The structural coefficient transition is the literal chart triangle component. -/
theorem chartPullbackCoefficientTransition_eq
    (F : AbelianSheaf.{u, u + 1} X)
    {U V : GeometricEtaleNeighborhood R Ω} (a : U ⟶ V) :
    pullbackCoefficientTransition (chartCoefficientDiagram R Ω j f)
        (chartCoefficientBaseCone R Ω j f) F a =
      (pullbackTriangleIso ((siteBaseChange f).obj
        ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω V))).hom
        ((siteBaseChange f).obj ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U))).hom
        ((siteBaseChange f).map ((Scheme.EtalePointOpen.postcompose j).map (etaleMap R Ω a))).left
        (MorphismProperty.Over.w ((siteBaseChange f).map
          ((Scheme.EtalePointOpen.postcompose j).map (etaleMap R Ω a))))).inv.app F :=
  pullbackCoefficientTransition_of_triangleIso_eq
    (chartCoefficientDiagram R Ω j f) (chartCoefficientBaseCone R Ω j f) F a _
    (chartPullbackTriangleIso_eq R Ω j f a)

variable [hExt : ∀ U : GeometricEtaleNeighborhood R Ω,
    HasExt.{e} (AbelianSheaf.{u, u + 1}
      (pullback ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)).hom f))]

local instance (U : GeometricEtaleNeighborhood R Ω) :
    HasExt.{e} (AbelianSheaf.{u, u + 1} ((chartCoefficientDiagram R Ω j f).obj U).unop) :=
  hExt U

/-- Original cohomology transfer respects the native geometric coefficient boundary. -/
theorem chartCohomologyTransfer_eq
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    {U V : GeometricEtaleNeighborhood R Ω} (a : U ⟶ V) :
    cohomologyTransfer ((chartCoefficientDiagram R Ω j f).map a).unop
        (pullbackCoefficientTransition (chartCoefficientDiagram R Ω j f)
          (chartCoefficientBaseCone R Ω j f) F a) q =
      AddCommGrpCat.ofHom (fibreProductCohomologyRestriction f
        ((Scheme.EtalePointOpen.postcompose j).map (etaleMap R Ω a)) F q) :=
  fibreProductCohomologyRestriction_of_heq f
    ((Scheme.EtalePointOpen.postcompose j).map (etaleMap R Ω a)) F
    ((chartCoefficientDiagram R Ω j f).map a).unop
    (chartCoefficientMap_eq R Ω j f a) _
    (heq_of_eq (chartPullbackCoefficientTransition_eq R Ω j f F a)) q

/-- The actual all-degree stage transition is the original fibre-product restriction. -/
theorem chartDiagramCohomologyMap_eq
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)
    {U V : GeometricEtaleNeighborhood R Ω} (a : U ⟶ V) :
    diagramCohomologyMap (chartCoefficientDiagram R Ω j f)
        (chartPullbackCoefficientSystem R Ω j f F) q a =
      AddCommGrpCat.ofHom (fibreProductCohomologyRestriction f
        ((Scheme.EtalePointOpen.postcompose j).map (etaleMap R Ω a)) F q) :=
  (diagramCohomologyMap_pullbackCoefficientSystem
    (chartCoefficientDiagram R Ω j f) (chartCoefficientBaseCone R Ω j f) F q a).trans
      (chartCohomologyTransfer_eq R Ω j f F q a)

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
