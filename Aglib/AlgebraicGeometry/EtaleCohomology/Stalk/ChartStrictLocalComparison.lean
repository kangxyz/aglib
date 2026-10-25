/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartCohomologyGerms
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartLimitContinuity

/-! # Original higher-direct-image stalks and strict-local cohomology -/

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
  [∀ U : S.Etale, HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  [HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f))]
  [QuasiCompact f] [QuasiSeparated f]
  [HasColimitsOfShape (GeometricEtaleNeighborhood R Ω) AddCommGrpCat.{e}]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

local instance chartStrictLocalConnected : IsConnected (GeometricEtaleNeighborhood R Ω) :=
  IsFiltered.isConnected (GeometricEtaleNeighborhood R Ω)

local instance chartStrictLocalRawStageExt (U : GeometricEtaleNeighborhood R Ω) :
    HasExt.{e} (AbelianSheaf.{u, u + 1}
      (pullback (Spec.algebraMap R U.algebra ≫ j) f)) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)).hom f)))

local instance chartStrictLocalDiagramStageExt (U : GeometricEtaleNeighborhood R Ω) :
    HasExt.{e} (AbelianSheaf.{u, u + 1} ((chartCoefficientDiagram R Ω j f).obj U).unop) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R U.algebra ≫ j) f)))

local instance chartStrictLocalLimitExt :
    HasExt.{e} (AbelianSheaf.{u, u + 1} (chartCoefficientLimitCocone R Ω j f).pt.unop) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f)))

/-- Compare the two actual lifted colimits; using the proved geometric continuity certificate. -/
def chartStrictLocalComparisonUliftIso :
    (chartOriginalStalkCocone R Ω j η hη f F q).pt ≅
      (AddCommGrpCat.uliftFunctor.{u + 1, e}.mapCocone
        (chartLimitCohomologyCocone R Ω j f F q)).pt :=
  (chartOriginalStalkCoconeIsColimit R Ω j η hη f F q).coconePointUniqueUpToIso
    (isColimitOfPreserves AddCommGrpCat.uliftFunctor.{u + 1, e}
      (chartLimitCohomologyCoconeIsColimit R Ω j f F q))

/-- The comparison is determined by the original two cocone legs. -/
theorem chartStrictLocalComparisonUliftIso_leg (U : GeometricEtaleNeighborhood R Ω) :
    (chartOriginalStalkCocone R Ω j η hη f F q).ι.app U ≫
        (chartStrictLocalComparisonUliftIso R Ω j η hη f F q).hom =
      AddCommGrpCat.uliftFunctor.{u + 1, e}.map
        ((chartLimitCohomologyCocone R Ω j f F q).ι.app U) :=
  IsColimit.comp_coconePointUniqueUpToIso_hom
    (chartOriginalStalkCoconeIsColimit R Ω j η hη f F q)
    (isColimitOfPreserves AddCommGrpCat.uliftFunctor.{u + 1, e}
      (chartLimitCohomologyCoconeIsColimit R Ω j f F q)) U

/-- Unlift to the original stalk and original strict-local cohomology groups. -/
def chartStrictLocalCohomologyAddEquiv :
    ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
        ((higherDirectImage f q).obj F) ≃+
      Sheaf.H.{e} ((inverseImage
        (pullback.snd (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f)).obj F) q :=
  AddEquiv.ulift.symm.trans
    ((chartStrictLocalComparisonUliftIso R Ω j η hη f F q).addCommGroupIsoToAddEquiv.trans
      AddEquiv.ulift)

/-- The comparison sends every original neighborhood germ to its canonical limit image. -/
theorem chartStrictLocalCohomologyAddEquiv_germ (U : GeometricEtaleNeighborhood R Ω)
    (x : Sheaf.H.{e} ((inverseImage (pullback.snd
      ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)).hom f)).obj F) q) :
    chartStrictLocalCohomologyAddEquiv R Ω j η hη f F q
      (fibreProductCohomologyGerm f
        ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)) F q
        η (chartStagePoint R Ω j η hη U) x) =
      (chartLimitCohomologyCocone R Ω j f F q).ι.app U x := by
  have h := ConcreteCategory.congr_hom
    (chartStrictLocalComparisonUliftIso_leg R Ω j η hη f F q U) (ULift.up x)
  have hsource := chartOriginalStalkCocone_apply R Ω j η hη f F q U x
  have h' := (congrArg
    ((chartStrictLocalComparisonUliftIso R Ω j η hη f F q).hom) hsource).symm.trans h
  exact congrArg ULift.down h'

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
