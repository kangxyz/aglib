/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.PullbackLimitCohomologyLeg
public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartPullbackCoefficient

/-! # The original cohomology cocone on the actual pointed-neighborhood limit -/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
universe u e
attribute [local instance] hasSheafifyLarge
open Continuity Finite.GeometricNeighborhood

variable (R Ω : Type u) [CommRing R] [Field Ω] [Algebra R Ω]
  {X S : Scheme.{u}} (j : Spec (.of R) ⟶ S) (f : X ⟶ S)
  [hExt : ∀ U : GeometricEtaleNeighborhood R Ω,
    HasExt.{e} (AbelianSheaf.{u, u + 1}
      (pullback (Spec.algebraMap R U.algebra ≫ j) f))]
  [HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f))]
  (F : AbelianSheaf.{u, u + 1} X) (q : ℕ)

local instance chartLimitCoconeConnected : IsConnected (GeometricEtaleNeighborhood R Ω) :=
  IsFiltered.isConnected (GeometricEtaleNeighborhood R Ω)

local instance chartLimitCoconeStageHasExt (U : GeometricEtaleNeighborhood R Ω) :
    HasExt.{e} (AbelianSheaf.{u, u + 1} ((chartCoefficientDiagram R Ω j f).obj U).unop) :=
  hExt U

local instance chartLimitCoconeApexHasExt :
    HasExt.{e} (AbelianSheaf.{u, u + 1} (chartCoefficientLimitCocone R Ω j f).pt.unop) :=
  inferInstanceAs (HasExt.{e} (AbelianSheaf.{u, u + 1}
    (pullback (Spec.algebraMap R (GeometricEtaleColimit R Ω) ≫ j) f)))

/-- The canonical system cocone with original strict-local pullback cohomology as apex.
Its universal property requires the separate cohomological continuity theorem. -/
def chartLimitCohomologyCocone :
    Cocone (diagramCohomologyFunctor (chartCoefficientDiagram R Ω j f)
      (chartPullbackCoefficientSystem R Ω j f F) q) :=
  pullbackLimitCohomologyCocone (chartCoefficientDiagram R Ω j f)
    (chartCoefficientBaseCone R Ω j f) (chartCoefficientLimitCocone R Ω j f)
    (chartGeometricBaseChangedCone R Ω j f).pt.hom.op
    (fun i => relativeCoefficient_cone_composite (chartGeometricBaseChangedDiagram R Ω j f)
      (chartGeometricBaseChangedCone R Ω j f)
      ((opOpEquivalence (GeometricEtaleNeighborhood R Ω)).inverse.obj i))
    F q

/-- The actual structural triangle sends a neighborhood class to the literal limit. -/
theorem chartLimitCohomologyCocone_leg (U : GeometricEtaleNeighborhood R Ω) :
    (chartLimitCohomologyCocone R Ω j f F q).ι.app U =
      pullbackLimitCohomologyLeg (chartCoefficientDiagram R Ω j f)
        (chartCoefficientBaseCone R Ω j f) (chartCoefficientLimitCocone R Ω j f)
        (chartGeometricBaseChangedCone R Ω j f).pt.hom.op
        (fun i => relativeCoefficient_cone_composite (chartGeometricBaseChangedDiagram R Ω j f)
          (chartGeometricBaseChangedCone R Ω j f)
          ((opOpEquivalence (GeometricEtaleNeighborhood R Ω)).inverse.obj i)) F q U :=
  pullbackLimitCohomologyCocone_leg_eq (chartCoefficientDiagram R Ω j f)
    (chartCoefficientBaseCone R Ω j f) (chartCoefficientLimitCocone R Ω j f)
    (chartGeometricBaseChangedCone R Ω j f).pt.hom.op
    (fun i => relativeCoefficient_cone_composite (chartGeometricBaseChangedDiagram R Ω j f)
      (chartGeometricBaseChangedCone R Ω j f)
      ((opOpEquivalence (GeometricEtaleNeighborhood R Ω)).inverse.obj i))
    F q U

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
