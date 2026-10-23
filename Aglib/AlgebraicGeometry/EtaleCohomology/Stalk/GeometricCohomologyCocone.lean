/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.CohomologyDiagramReindex
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GeometricOriginalDiagram
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GeometricCohomologyStalk

/-! # Original geometric cohomology cocones with their native stalk apex -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe u w s e
attribute [local instance] hasSheafifyLarge
open Continuity Finite.GeometricNeighborhood

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω] [IsSepClosed Ω]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : (Spec (.of R)).Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [∀ U : (Spec (.of R)).Etale,
    HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

local instance (U : GeometricEtaleNeighborhood R Ω) :
    HasExt.{e} (AbelianSheaf.{u, u + 1} ((geometricCoefficientDiagram R Ω f).obj U).unop) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback (etaleObject R Ω U).hom f)))

/-- Original system H and the native stalk diagram agree in a common universe. -/
def geometricCohomologyUliftIso :
    diagramCohomologyFunctor (geometricCoefficientDiagram R Ω f)
        (geometricPullbackCoefficientSystem R Ω f F) q ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, e} ≅
      sectionDiagram R Ω (smallFibreProductCohomologyPresheaf f F q) ⋙
        AddCommGrpCat.uliftFunctor.{e, u + 1} :=
  additiveTwiceReindexUliftIso
    (toStalkIndex R Ω)
    (Functor.Elements.π (pointSmallEtale (Spec.algebraMap R Ω)).fiber).op
    (diagramCohomologyFunctor (geometricCoefficientDiagram R Ω f)
      (geometricPullbackCoefficientSystem R Ω f F) q)
    (originalFibreProductCohomologyPresheaf f F q)
    (smallFibreProductCohomologyPresheaf f F q)
    (geometricOriginalCohomologyIso R Ω f F q) (originalFibreProductUliftIso f F q)

/-- The actual small cohomology cocone with its native higher-image stalk apex. -/
def geometricNativeStalkCocone :
    Cocone (sectionDiagram R Ω (smallFibreProductCohomologyPresheaf f F q)) :=
  (colimit.cocone _).extend (geometricCohomologyStalkIso R Ω f F q).hom

/-- The original germ cocone is colimiting, by its actual stalk comparison. -/
def geometricNativeStalkCoconeIsColimit :
    IsColimit (geometricNativeStalkCocone R Ω f F q) :=
  IsColimit.extendIso (geometricCohomologyStalkIso R Ω f F q).hom (colimit.isColimit _)

/-- Lift the native germ cocone and transport along the original whole-diagram comparison. -/
def geometricOriginalStalkCocone :
    Cocone (diagramCohomologyFunctor (geometricCoefficientDiagram R Ω f)
      (geometricPullbackCoefficientSystem R Ω f F) q ⋙ AddCommGrpCat.uliftFunctor.{u + 1, e}) :=
  (Cocone.precompose (geometricCohomologyUliftIso R Ω f F q).hom).obj
    (AddCommGrpCat.uliftFunctor.{e, u + 1}.mapCocone (geometricNativeStalkCocone R Ω f F q))

/-- The original lifted system-H cocone is genuinely colimiting.
This uses preservation of the native germ cocone, not strict-local continuity. -/
def geometricOriginalStalkCoconeIsColimit :
    IsColimit (geometricOriginalStalkCocone R Ω f F q) :=
  (IsColimit.precomposeHomEquiv (geometricCohomologyUliftIso R Ω f F q) _).symm
    (isColimitOfPreserves AddCommGrpCat.uliftFunctor.{e, u + 1}
      (geometricNativeStalkCoconeIsColimit R Ω f F q))

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
