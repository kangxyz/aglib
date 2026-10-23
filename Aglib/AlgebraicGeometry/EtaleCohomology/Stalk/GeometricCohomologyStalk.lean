/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.FibreProductStalk
public import Aglib.AlgebraicGeometry.EtaleCohomology.Finite.GeometricNeighborhoodStalk

/-! # Actual geometric-system cohomology classes and native higher-image germs -/

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

/-- The actual geometric cohomology diagram computes the native higher-image stalk.
This is a neighborhood-colimit theorem, not strict-local cohomological continuity. -/
def geometricCohomologyStalkIso :
    colimit (sectionDiagram R Ω (smallFibreProductCohomologyPresheaf f F q)) ≅
      ((pointSmallEtale (Spec.algebraMap R Ω)).sheafFiber (A := AddCommGrpCat.{u + 1})).obj
        ((higherDirectImage f q).obj F) :=
  stalkIso R Ω (smallFibreProductCohomologyPresheaf f F q) ≪≫
    fibreProductCohomologyStalkIso f F q (Spec.algebraMap R Ω)

/-- Every unresized original class maps to its literal original higher-image germ. -/
theorem ι_geometricCohomologyStalkIso_apply (U : GeometricEtaleNeighborhood R Ω)
    (x : Sheaf.H.{e} ((inverseImage (pullback.snd (etaleObject R Ω U).hom f)).obj F) q) :
    (geometricCohomologyStalkIso R Ω f F q).hom
        (colimit.ι (sectionDiagram R Ω (smallFibreProductCohomologyPresheaf f F q)) U
          (Shrink.addEquiv.symm x)) =
      fibreProductCohomologyGerm f (etaleObject R Ω U) F q
        (Spec.algebraMap R Ω) (stagePoint R Ω U) x := by
  have h := ConcreteCategory.congr_hom
    (ι_stalkIso_hom R Ω (smallFibreProductCohomologyPresheaf f F q) U)
    (Shrink.addEquiv.symm x)
  exact (congrArg (fibreProductCohomologyStalkIso f F q (Spec.algebraMap R Ω)).hom h).trans
    (germ_fibreProductCohomologyStalkIso_apply f F q (Spec.algebraMap R Ω)
      (etaleObject R Ω U) (stagePoint R Ω U) x)

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
