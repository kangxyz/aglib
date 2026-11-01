/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Stalk.ChartLimitContinuity
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered

/-! # Eventual vanishing of original classes on pointed etale neighborhoods

The existing original-cohomology limit cocone is used without replacing its
apex or its legs. Forgetting its filtered colimit to types detects equality
with zero at an actual later neighborhood.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Stalk

universe u e uI vI
attribute [local instance] hasSheafifyLarge
open Continuity Finite.GeometricNeighborhood

attribute [local instance] hasExtStandard

/-- Original vanishing on the actual neighborhood limit spreads to an actual
pointed etale stage, for any degree and any fixed sheaf on a qcqs morphism. -/
theorem exists_chart_cohomologyPullback_eq_zero
    (R k : Type u) [CommRing R] [Field k] [Algebra R k]
    {X S : Scheme.{u}} (j : Spec (.of R) ⟶ S) (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f]
    (F : AbelianSheaf.{u, u + 1} X) (q : ℕ) (δ : Sheaf.H.{u + 2} F q)
    (hδ : cohomologyPullback
      (pullback.snd (Spec.algebraMap R (GeometricEtaleColimit R k) ≫ j) f) F q δ = 0) :
    ∃ U : GeometricEtaleNeighborhood R k,
      cohomologyPullback (pullback.snd (Spec.algebraMap R U.algebra ≫ j) f) F q δ = 0 := by
  let : IsConnected (GeometricEtaleNeighborhood R k) :=
    IsFiltered.isConnected (GeometricEtaleNeighborhood R k)
  let : PreservesFilteredColimitsOfSize.{u, u} (CategoryTheory.forget AddCommGrpCat.{u + 2}) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 2, u + 2}
      (CategoryTheory.forget AddCommGrpCat.{u + 2})
  exact exists_pullback_eq_zero_of_colimit
    (chartCoefficientDiagram R k j f) (chartCoefficientBaseCone R k j f)
    (chartCoefficientLimitCocone R k j f)
    (chartGeometricBaseChangedCone R k j f).pt.hom.op
    (fun i => relativeCoefficient_cone_composite (chartGeometricBaseChangedDiagram R k j f)
      (chartGeometricBaseChangedCone R k j f)
      ((opOpEquivalence (GeometricEtaleNeighborhood R k)).inverse.obj i)) F q
    (chartLimitCohomologyCoconeIsColimit R k j f F q) δ hδ

end AlgebraicGeometry.Scheme.EtaleCohomology.Stalk
