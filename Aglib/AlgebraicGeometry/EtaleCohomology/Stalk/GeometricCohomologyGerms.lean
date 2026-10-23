/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.CohomologyUliftComponents
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GeometricCohomologyCocone

/-! # Literal original classes in the geometric system-H germ cocone -/

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

/-- The lifted whole-diagram comparison retains each original unresized class. -/
theorem geometricCohomologyUliftIso_apply (U : GeometricEtaleNeighborhood R Ω)
    (x : Sheaf.H.{e} ((inverseImage (pullback.snd (etaleObject R Ω U).hom f)).obj F) q) :
    (geometricCohomologyUliftIso R Ω f F q).hom.app U (ULift.up x) =
      ULift.up (Shrink.addEquiv.symm x) := by
  have h := additiveTwiceReindexUliftIso_apply
    (toStalkIndex R Ω)
    (Functor.Elements.π (pointSmallEtale (Spec.algebraMap R Ω)).fiber).op
    (diagramCohomologyFunctor (geometricCoefficientDiagram R Ω f)
      (geometricPullbackCoefficientSystem R Ω f F) q)
    (originalFibreProductCohomologyPresheaf f F q)
    (smallFibreProductCohomologyPresheaf f F q)
    (geometricOriginalCohomologyIso R Ω f F q) (originalFibreProductUliftIso f F q) U x
  exact h.trans (originalFibreProductUliftIso_apply f F q (op (etaleObject R Ω U)) x)

/-- The small native cocone sends the resized original class to its literal germ. -/
theorem geometricNativeStalkCocone_apply (U : GeometricEtaleNeighborhood R Ω)
    (x : Sheaf.H.{e} ((inverseImage (pullback.snd (etaleObject R Ω U).hom f)).obj F) q) :
    (geometricNativeStalkCocone R Ω f F q).ι.app U (Shrink.addEquiv.symm x) =
      fibreProductCohomologyGerm f (etaleObject R Ω U) F q
        (Spec.algebraMap R Ω) (stagePoint R Ω U) x :=
  ι_geometricCohomologyStalkIso_apply R Ω f F q U x

/-- Every original system-H class has its original higher-image germ in the lifted cocone. -/
theorem geometricOriginalStalkCocone_apply (U : GeometricEtaleNeighborhood R Ω)
    (x : Sheaf.H.{e} ((inverseImage (pullback.snd (etaleObject R Ω U).hom f)).obj F) q) :
    (geometricOriginalStalkCocone R Ω f F q).ι.app U (ULift.up x) =
      ULift.up (fibreProductCohomologyGerm f (etaleObject R Ω U) F q
        (Spec.algebraMap R Ω) (stagePoint R Ω U) x) := by
  have h := congrArg
    (AddCommGrpCat.uliftFunctor.{e, u + 1}.map
      ((geometricNativeStalkCocone R Ω f F q).ι.app U))
    (geometricCohomologyUliftIso_apply R Ω f F q U x)
  exact h.trans (congrArg ULift.up (geometricNativeStalkCocone_apply R Ω f F q U x))

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
