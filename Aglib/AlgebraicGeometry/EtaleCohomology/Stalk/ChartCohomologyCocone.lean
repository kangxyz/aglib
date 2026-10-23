/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.CohomologyDiagramReindex
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartOriginalDiagram
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartCohomologyStalk

/-! # Original geometric cohomology cocones with their native stalk apex -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe u w s e
attribute [local instance] hasSheafifyLarge
open Continuity Finite.GeometricNeighborhood

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsSepClosed Ω]
  {X S : Scheme.{u}} (j : Spec (.of R) ⟶ S) [Etale j] [Mono j]
  (η : Spec (.of Ω) ⟶ S) (hη : Spec.algebraMap R Ω ≫ j = η) (f : X ⟶ S)
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : S.Etale,
    HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

local instance (U : GeometricEtaleNeighborhood R Ω) :
    HasExt.{e} (AbelianSheaf.{u, u + 1} ((chartCoefficientDiagram R Ω j f).obj U).unop) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)).hom f)))

omit [Mono j] in
/-- Original system H and the native stalk diagram agree in a common universe. -/
def chartCohomologyUliftIso :
    diagramCohomologyFunctor (chartCoefficientDiagram R Ω j f)
        (chartPullbackCoefficientSystem R Ω j f F) q ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, e} ≅
      chartSectionDiagram R Ω j η hη (smallFibreProductCohomologyPresheaf f F q) ⋙
        AddCommGrpCat.uliftFunctor.{e, u + 1} :=
  additiveTwiceReindexUliftIso
    (chartToStalkIndex R Ω j η hη)
    (Functor.Elements.π (pointSmallEtale η).fiber).op
    (diagramCohomologyFunctor (chartCoefficientDiagram R Ω j f)
      (chartPullbackCoefficientSystem R Ω j f F) q)
    (originalFibreProductCohomologyPresheaf f F q)
    (smallFibreProductCohomologyPresheaf f F q)
    (chartOriginalCohomologyIso R Ω j η hη f F q) (originalFibreProductUliftIso f F q)

/-- The actual small cohomology cocone with its native higher-image stalk apex. -/
def chartNativeStalkCocone :
    Cocone (chartSectionDiagram R Ω j η hη (smallFibreProductCohomologyPresheaf f F q)) :=
  (colimit.cocone _).extend (chartCohomologyStalkIso R Ω j η hη f F q).hom

/-- The original germ cocone is colimiting, by its actual stalk comparison. -/
def chartNativeStalkCoconeIsColimit :
    IsColimit (chartNativeStalkCocone R Ω j η hη f F q) :=
  IsColimit.extendIso (chartCohomologyStalkIso R Ω j η hη f F q).hom (colimit.isColimit _)

/-- Lift the native germ cocone and transport along the original whole-diagram comparison. -/
def chartOriginalStalkCocone :
    Cocone (diagramCohomologyFunctor (chartCoefficientDiagram R Ω j f)
      (chartPullbackCoefficientSystem R Ω j f F) q ⋙ AddCommGrpCat.uliftFunctor.{u + 1, e}) :=
  (Cocone.precompose (chartCohomologyUliftIso R Ω j η hη f F q).hom).obj
    (AddCommGrpCat.uliftFunctor.{e, u + 1}.mapCocone (chartNativeStalkCocone R Ω j η hη f F q))

/-- The original lifted system-H cocone is genuinely colimiting.
This uses preservation of the native germ cocone, not strict-local continuity. -/
def chartOriginalStalkCoconeIsColimit :
    IsColimit (chartOriginalStalkCocone R Ω j η hη f F q) :=
  (IsColimit.precomposeHomEquiv (chartCohomologyUliftIso R Ω j η hη f F q) _).symm
    (isColimitOfPreserves AddCommGrpCat.uliftFunctor.{e, u + 1}
      (chartNativeStalkCoconeIsColimit R Ω j η hη f F q))

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
