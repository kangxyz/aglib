/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/

module

public import Aglib.Topology.Algebra.Group.StableQuotient

/-!
# Actual continuous coefficient projection through a stable subgroup

The arbitrary subgroup is not assumed closed, and no Hausdorff condition is added.
-/

@[expose] public section

open GroupCohomology.ContinuousH1 AddSubgroup.StableQuotient

variable {G M : Type*} [Group G] [AddCommGroup M] [DistribMulAction G M]
  [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [ContinuousSMul G M]
  (R : AddSubgroup M) (hstable : ∀ (g : G) (k : M), k ∈ R → g • k ∈ R)

/-- The quotient action composes the two original actions on the same representative. -/
example (g h : G) (m : M) :
    let := action R hstable
    (g * h) • QuotientAddGroup.mk' R m = QuotientAddGroup.mk' R (g • h • m) := by
  let := action R hstable
  exact (action_mk R hstable (g * h) m).trans
    (congrArg (QuotientAddGroup.mk' R) (mul_smul g h m))

/-- The genuine continuous quotient map sends a cocycle to its pointwise projection. -/
example (c : Cocycle G M) (g : G) :
    let := action R hstable
    let := continuousAction R hstable
    ((coefficientProjection R hstable).onCocycles c).val g =
      QuotientAddGroup.mk' R (c.val g) := rfl

/-- The same actual coefficient projection sends a principal class to zero in
continuous H1, using no geometric realization or quotient comparison assumption. -/
example (m : M) :
    let := action R hstable
    let := continuousAction R hstable
    (coefficientProjection R hstable).onH1 (classOf G M (principal G M m)) = 0 := by
  let := action R hstable
  let := continuousAction R hstable
  let f := (coefficientProjection R hstable).onH1
  exact (congrArg f (classOf_principal G M m)).trans f.map_zero
