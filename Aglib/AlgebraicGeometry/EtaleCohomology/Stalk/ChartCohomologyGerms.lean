/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.CohomologyUliftComponents
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartCohomologyCocone

/-! # Literal original classes in the geometric system-H germ cocone -/

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
/-- The lifted whole-diagram comparison retains each original unresized class. -/
theorem chartCohomologyUliftIso_apply (U : GeometricEtaleNeighborhood R Ω)
    (x : Sheaf.H.{e} ((inverseImage (pullback.snd
      ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)).hom f)).obj F) q) :
    (chartCohomologyUliftIso R Ω j η hη f F q).hom.app U (ULift.up x) =
      ULift.up (Shrink.addEquiv.symm x) := by
  have h := additiveTwiceReindexUliftIso_apply
    (chartToStalkIndex R Ω j η hη)
    (Functor.Elements.π (pointSmallEtale η).fiber).op
    (diagramCohomologyFunctor (chartCoefficientDiagram R Ω j f)
      (chartPullbackCoefficientSystem R Ω j f F) q)
    (originalFibreProductCohomologyPresheaf f F q)
    (smallFibreProductCohomologyPresheaf f F q)
    (chartOriginalCohomologyIso R Ω j η hη f F q) (originalFibreProductUliftIso f F q) U x
  exact h.trans (originalFibreProductUliftIso_apply f F q
    (op ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U))) x)

/-- The small native cocone sends the resized original class to its literal germ. -/
theorem chartNativeStalkCocone_apply (U : GeometricEtaleNeighborhood R Ω)
    (x : Sheaf.H.{e} ((inverseImage (pullback.snd
      ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)).hom f)).obj F) q) :
    (chartNativeStalkCocone R Ω j η hη f F q).ι.app U (Shrink.addEquiv.symm x) =
      fibreProductCohomologyGerm f
        ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)) F q
        η (chartStagePoint R Ω j η hη U) x :=
  ι_chartCohomologyStalkIso_apply R Ω j η hη f F q U x

/-- Every original system-H class has its original higher-image germ in the lifted cocone. -/
theorem chartOriginalStalkCocone_apply (U : GeometricEtaleNeighborhood R Ω)
    (x : Sheaf.H.{e} ((inverseImage (pullback.snd
      ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)).hom f)).obj F) q) :
    (chartOriginalStalkCocone R Ω j η hη f F q).ι.app U (ULift.up x) =
      ULift.up (fibreProductCohomologyGerm f
        ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)) F q
        η (chartStagePoint R Ω j η hη U) x) := by
  have h := congrArg
    (AddCommGrpCat.uliftFunctor.{e, u + 1}.map
      ((chartNativeStalkCocone R Ω j η hη f F q).ι.app U))
    (chartCohomologyUliftIso_apply R Ω j η hη f F q U x)
  exact h.trans (congrArg ULift.up (chartNativeStalkCocone_apply R Ω j η hη f F q U x))

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
