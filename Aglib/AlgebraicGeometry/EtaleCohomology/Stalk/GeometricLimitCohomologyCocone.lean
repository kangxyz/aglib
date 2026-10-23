/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PullbackLimitCohomologyLeg
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.GeometricPullbackCoefficient

/-! # The original cohomology cocone on the actual pointed-neighborhood limit -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe u e
attribute [local instance] hasSheafifyLarge
open Continuity Finite.GeometricNeighborhood

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
  {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
  [∀ U : (Spec (.of R)).Etale,
    HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback U.hom f))]
  [HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω)) f))]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

local instance geometricLimitCocone_indexConnected : IsConnected (GeometricEtaleNeighborhood R Ω) :=
  IsFiltered.isConnected (GeometricEtaleNeighborhood R Ω)

local instance geometricLimitCocone_stageHasExt (U : GeometricEtaleNeighborhood R Ω) :
    HasExt.{e} (AbelianSheaf.{u, u + 1} ((geometricCoefficientDiagram R Ω f).obj U).unop) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1} (pullback (etaleObject R Ω U).hom f)))

local instance geometricLimitCocone_pointHasExt :
    HasExt.{e} (AbelianSheaf.{u, u + 1} (geometricCoefficientLimitCocone R Ω f).pt.unop) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω)) f)))

/-- The canonical system cocone with original strict-local pullback cohomology as apex.
Its universal property requires the separate cohomological continuity theorem. -/
def geometricLimitCohomologyCocone :
    Cocone (diagramCohomologyFunctor (geometricCoefficientDiagram R Ω f)
      (geometricPullbackCoefficientSystem R Ω f F) q) :=
  pullbackLimitCohomologyCocone (geometricCoefficientDiagram R Ω f)
    (geometricCoefficientBaseCone R Ω f) (geometricCoefficientLimitCocone R Ω f)
    (baseChangedCone R Ω f).pt.hom.op
    (fun i => relativeCoefficient_cone_composite (baseChangedDiagram R Ω f)
      (baseChangedCone R Ω f) ((opOpEquivalence (GeometricEtaleNeighborhood R Ω)).inverse.obj i))
    F q

/-- The actual structural triangle sends a neighborhood class to the literal limit. -/
theorem geometricLimitCohomologyCocone_leg (U : GeometricEtaleNeighborhood R Ω) :
    (geometricLimitCohomologyCocone R Ω f F q).ι.app U =
      pullbackLimitCohomologyLeg (geometricCoefficientDiagram R Ω f)
        (geometricCoefficientBaseCone R Ω f) (geometricCoefficientLimitCocone R Ω f)
        (baseChangedCone R Ω f).pt.hom.op
        (fun i => relativeCoefficient_cone_composite (baseChangedDiagram R Ω f)
          (baseChangedCone R Ω f)
          ((opOpEquivalence (GeometricEtaleNeighborhood R Ω)).inverse.obj i)) F q U :=
  pullbackLimitCohomologyCocone_leg_eq (geometricCoefficientDiagram R Ω f)
    (geometricCoefficientBaseCone R Ω f) (geometricCoefficientLimitCocone R Ω f)
    (baseChangedCone R Ω f).pt.hom.op
    (fun i => relativeCoefficient_cone_composite (baseChangedDiagram R Ω f)
      (baseChangedCone R Ω f) ((opOpEquivalence (GeometricEtaleNeighborhood R Ω)).inverse.obj i))
    F q U

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
