/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductStalk
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartGeometricStalkIndex

/-! # Actual geometric-system cohomology classes and native higher-image germs -/

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

/-- The actual geometric cohomology diagram computes the native higher-image stalk.
This is a neighborhood-colimit theorem, not strict-local cohomological continuity. -/
def chartCohomologyStalkIso :
    colimit (chartSectionDiagram R Ω j η hη (smallFibreProductCohomologyPresheaf f F q)) ≅
      ((pointSmallEtale η).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
        ((higherDirectImage f q).obj F) :=
  chartPresheafStalkIso R Ω j η hη (smallFibreProductCohomologyPresheaf f F q) ≪≫
    fibreProductCohomologyStalkIso f F q η

/-- Every unresized original class maps to its literal original higher-image germ. -/
theorem ι_chartCohomologyStalkIso_apply (U : GeometricEtaleNeighborhood R Ω)
    (x : Sheaf.H.{e} ((inverseImage (pullback.snd
      ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)).hom f)).obj F) q) :
    (chartCohomologyStalkIso R Ω j η hη f F q).hom
        (colimit.ι
          (chartSectionDiagram R Ω j η hη (smallFibreProductCohomologyPresheaf f F q)) U
          (Shrink.addEquiv.symm x)) =
      fibreProductCohomologyGerm f
        ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U)) F q
        η (chartStagePoint R Ω j η hη U) x := by
  have h := ConcreteCategory.congr_hom
    (ι_chartPresheafStalkIso_hom R Ω j η hη (smallFibreProductCohomologyPresheaf f F q) U)
    (Shrink.addEquiv.symm x)
  exact (congrArg (fibreProductCohomologyStalkIso f F q η).hom h).trans
    (germ_fibreProductCohomologyStalkIso_apply f F q η
      ((Scheme.EtalePointOpen.postcompose j).obj (etaleObject R Ω U))
      (chartStagePoint R Ω j η hη U) x)

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
