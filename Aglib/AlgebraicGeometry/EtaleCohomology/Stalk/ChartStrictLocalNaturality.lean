/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartStrictLocalComparison
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PullbackLimitLegNaturality
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductGermNaturality
public import Aglib.CategoryTheory.Limits.CoconeValues
public import Aglib.Algebra.Category.Grp.Resize.Naturality
/-! # Coefficient naturality of the original strict-local comparison -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe u w s e
attribute [local instance] hasSheafifyLarge
open Continuity Finite.GeometricNeighborhood
section UliftNaturality
universe uA uB
variable {A A' : AddCommGrpCat.{uA}} {B B' : AddCommGrpCat.{uB}}

/-- Unlift a naturality square without expanding its concrete cohomology groups. -/
theorem uliftComparison_naturality
    (E : AddCommGrpCat.uliftFunctor.{uB, uA}.obj A ≅
      AddCommGrpCat.uliftFunctor.{uA, uB}.obj B)
    (E' : AddCommGrpCat.uliftFunctor.{uB, uA}.obj A' ≅
      AddCommGrpCat.uliftFunctor.{uA, uB}.obj B')
    (a : A ⟶ A') (b : B ⟶ B')
    (h : E.hom ≫ AddCommGrpCat.uliftFunctor.map b =
      AddCommGrpCat.uliftFunctor.map a ≫ E'.hom) (x : A) :
    b ((AddEquiv.ulift.symm.trans
      (E.addCommGroupIsoToAddEquiv.trans AddEquiv.ulift)) x) =
    (AddEquiv.ulift.symm.trans
      (E'.addCommGroupIsoToAddEquiv.trans AddEquiv.ulift)) (a x) :=
  AddCommGrpCat.uliftComparison_naturality E E' a b h x
end UliftNaturality

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
  {F G : AbelianSheaf.{u, u + 1} X} (g : F ⟶ G) (q : ℕ)

local instance chartCoefficientNaturalConnected : IsConnected (GeometricEtaleNeighborhood R Ω) :=
  IsFiltered.isConnected (GeometricEtaleNeighborhood R Ω)

local instance chartCoefficientNaturalRawStageExt (U : GeometricEtaleNeighborhood R Ω) :
    HasExt.{e} (AbelianSheaf.{u, u + 1}
      (pullback (Spec.algebraMap R U.algebra ≫ j) f)) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)).hom f)))

local instance chartCoefficientNaturalDiagramStageExt (U : GeometricEtaleNeighborhood R Ω) :
    HasExt.{e} (AbelianSheaf.{u, u + 1} ((chartCoefficientDiagram R Ω j f).obj U).unop) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R U.algebra ≫ j) f)))

local instance chartCoefficientNaturalLimitExt :
    HasExt.{e} (AbelianSheaf.{u, u + 1} (chartCoefficientLimitCocone R Ω j f).pt.unop) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f)))


omit [IsSepClosed Ω] [Mono j] [QuasiCompact f] [QuasiSeparated f]
  [HasExt.{w} (AbelianSheaf.{u, u + 1} X)]
  [∀ U : S.Etale, HasExt.{s} (Sheaf ((Scheme.smallEtaleTopology X).over
    ((siteBaseChange f).obj U)) AddCommGrpCat.{u + 1})]
  [HasColimitsOfShape (GeometricEtaleNeighborhood R Ω) AddCommGrpCat.{e}] in
/-- Original limit legs respect the original inverse-image coefficient maps. -/
theorem chartLimitCohomologyCocone_naturality (U : GeometricEtaleNeighborhood R Ω) :
    (chartLimitCohomologyCocone R Ω j f F q).ι.app U ≫
      AddCommGrpCat.ofHom (Sheaf.H.map ((inverseImage
        (pullback.snd (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f)).map g) q) =
    AddCommGrpCat.ofHom (Sheaf.H.map ((inverseImage (pullback.snd
      ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)).hom f)).map g) q) ≫
      (chartLimitCohomologyCocone R Ω j f G q).ι.app U := by
  rw [chartLimitCohomologyCocone_leg, chartLimitCohomologyCocone_leg]
  exact pullbackLimitCohomologyLeg_naturality (chartCoefficientDiagram R Ω j f)
    (chartCoefficientBaseCone R Ω j f) (chartCoefficientLimitCocone R Ω j f)
    (chartGeometricBaseChangedCone R Ω j f).pt.hom.op
    (fun i => relativeCoefficient_cone_composite (chartGeometricBaseChangedDiagram R Ω j f)
      (chartGeometricBaseChangedCone R Ω j f)
      ((opOpEquivalence (GeometricEtaleNeighborhood R Ω)).inverse.obj i)) g q U

/-- Naturality of the SAME original uniqueness comparisons, from both actual leg squares. -/
theorem chartStrictLocalComparisonUliftIso_naturality :
    (chartStrictLocalComparisonUliftIso R Ω j η hη f F q).hom ≫
        AddCommGrpCat.uliftFunctor.{u + 1, e}.map
          (AddCommGrpCat.ofHom (Sheaf.H.map ((inverseImage
            (pullback.snd (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f)).map g) q)) =
      AddCommGrpCat.uliftFunctor.{e, u + 1}.map
        (((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).map
          ((higherDirectImage f q).map g)) ≫
        (chartStrictLocalComparisonUliftIso R Ω j η hη f G q).hom := by
  let a := ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).map
    ((higherDirectImage f q).map g)
  let b := AddCommGrpCat.ofHom (Sheaf.H.map ((inverseImage
    (pullback.snd (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f)).map g) q)
  let φ (U : GeometricEtaleNeighborhood R Ω) :
      AddCommGrpCat.of (Sheaf.H.{e} ((inverseImage (pullback.snd
        ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)).hom f)).obj F) q) ⟶
      AddCommGrpCat.of (Sheaf.H.{e} ((inverseImage (pullback.snd
        ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)).hom f)).obj G) q) :=
    AddCommGrpCat.ofHom (Sheaf.H.map ((inverseImage (pullback.snd
      ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)).hom f)).map g) q)
  exact CoconeValues.coconePointUniqueUpToIso_naturality
    (chartOriginalStalkCoconeIsColimit R Ω j η hη f F q)
    (isColimitOfPreserves AddCommGrpCat.uliftFunctor.{u + 1, e}
      (chartLimitCohomologyCoconeIsColimit R Ω j f F q))
    (chartOriginalStalkCoconeIsColimit R Ω j η hη f G q)
    (isColimitOfPreserves AddCommGrpCat.uliftFunctor.{u + 1, e}
      (chartLimitCohomologyCoconeIsColimit R Ω j f G q))
    (fun U => AddCommGrpCat.uliftFunctor.{u + 1, e}.map (φ U))
    (AddCommGrpCat.uliftFunctor.{e, u + 1}.map a)
    (AddCommGrpCat.uliftFunctor.{u + 1, e}.map b)
    (fun U => by
      apply ConcreteCategory.hom_ext
      intro x
      obtain ⟨x⟩ := x
      have hsource := chartOriginalStalkCocone_apply R Ω j η hη f F q U x
      have htarget := chartOriginalStalkCocone_apply R Ω j η hη f G q U ((φ U).hom x)
      have hgerm := fibreProductCohomologyGerm_naturality f
        ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)) g q
        η (chartStagePoint R Ω j η hη U) x
      exact (congrArg (AddCommGrpCat.uliftFunctor.{e, u + 1}.map a) hsource).trans
        ((congrArg ULift.up hgerm).trans htarget.symm))
    (fun U => by
      have hmap := congrArg (fun z => AddCommGrpCat.uliftFunctor.{u + 1, e}.map z)
        (chartLimitCohomologyCocone_naturality R Ω j f g q U)
      have hleft := (AddCommGrpCat.uliftFunctor.{u + 1, e}.map_comp
        ((chartLimitCohomologyCocone R Ω j f F q).ι.app U) b).symm
      have hright := AddCommGrpCat.uliftFunctor.{u + 1, e}.map_comp (φ U)
        ((chartLimitCohomologyCocone R Ω j f G q).ι.app U)
      have hfinal := hleft.trans (hmap.trans hright)
      exact hfinal)

/-- The whole original comparison square on an actual neighborhood leg. -/
theorem chartStrictLocalComparisonUliftIso_naturality_leg
    (U : GeometricEtaleNeighborhood R Ω) :
    (chartOriginalStalkCocone R Ω j η hη f F q).ι.app U ≫
        (chartStrictLocalComparisonUliftIso R Ω j η hη f F q).hom ≫
          AddCommGrpCat.uliftFunctor.{u + 1, e}.map
            (AddCommGrpCat.ofHom (Sheaf.H.map ((inverseImage
              (pullback.snd (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f)).map g) q)) =
      (chartOriginalStalkCocone R Ω j η hη f F q).ι.app U ≫
        AddCommGrpCat.uliftFunctor.{e, u + 1}.map
          (((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).map
            ((higherDirectImage f q).map g)) ≫
          (chartStrictLocalComparisonUliftIso R Ω j η hη f G q).hom := by
  have h := congrArg (fun z => (chartOriginalStalkCocone R Ω j η hη f F q).ι.app U ≫ z)
    (chartStrictLocalComparisonUliftIso_naturality R Ω j η hη f g q)
  exact h

/-- Naturality of the original stalk-to-strict-local-cohomology comparison. -/
theorem chartStrictLocalCohomologyAddEquiv_naturality
    (z : ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
      ((higherDirectImage f q).obj F)) :
    Sheaf.H.map ((inverseImage
        (pullback.snd (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f)).map g) q
      (chartStrictLocalCohomologyAddEquiv R Ω j η hη f F q z) =
    chartStrictLocalCohomologyAddEquiv R Ω j η hη f G q
      (((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).map
        ((higherDirectImage f q).map g) z) := by
  exact uliftComparison_naturality
    (chartStrictLocalComparisonUliftIso R Ω j η hη f F q)
    (chartStrictLocalComparisonUliftIso R Ω j η hη f G q)
    (((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).map
      ((higherDirectImage f q).map g))
    (AddCommGrpCat.ofHom (Sheaf.H.map ((inverseImage
      (pullback.snd (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f)).map g) q))
    (chartStrictLocalComparisonUliftIso_naturality R Ω j η hη f g q) z
end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
