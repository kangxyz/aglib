/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Curves.GenericEtalePointLifting
public import Aglib.AlgebraicGeometry.Morphisms.Etale.QuasiFinite
public import Aglib.Topology.GenericOrClosedDimension
public import Aglib.Topology.NoetherianCurveSupport

/-! # Actual etale tests of a locally Noetherian curve have dimension at most one -/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Curves

universe u

private theorem closed_point_of_closed_image {U X : Scheme.{u}} (f : U ⟶ X)
    [LocallyQuasiFinite f] (y : U) (hy : IsClosed ({f y} : Set X)) :
    IsClosed ({y} : Set U) := by
  let Z : Set U := f ⁻¹' {f y}
  have hZ : IsClosed Z := hy.preimage f.continuous
  let : DiscreteTopology Z :=
    isDiscrete_iff_discreteTopology.mp (f.isDiscrete_preimage_singleton (f y))
  have h := hZ.isClosedEmbedding_subtypeVal.isClosedMap
    ({⟨y, rfl⟩} : Set Z) (isClosed_singleton (x := (⟨y, rfl⟩ : Z)))
  simpa only [Set.image_singleton] using h

/-- No quasi-compactness or reducedness is needed for the dimension bound on the etale test. -/
theorem topologicalKrullDim_le_one_of_etale {U X : Scheme.{u}} (f : U ⟶ X)
    [IsLocallyNoetherian X] [Etale f] (hdim : topologicalKrullDim X ≤ 1) :
    topologicalKrullDim U ≤ 1 := by
  apply topologicalKrullDim_le_one_of_generic_or_closed
  intro y
  by_cases hy : f y ∈ genericPoints X
  · exact Or.inl (mem_genericPoints_of_etale_image f y hy)
  · exact Or.inr (closed_point_of_closed_image f y
      (isClosed_singleton_of_not_generic_of_dim_le_one hdim hy))

end AlgebraicGeometry.Scheme.EtaleCohomology.Curves
