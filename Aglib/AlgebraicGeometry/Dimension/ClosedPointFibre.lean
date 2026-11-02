/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.Topology.KrullDimension.ClosedSubspace
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Properties

/-! # Strict dimension drop for actual closed point fibres

A proper closed subscheme of an integral scheme avoids its unique generic
point and lowers a finite dimension bound by one. For a surjective morphism
to a nontrivial target, every closed field-valued point has such a proper
closed fibre. No properness, finite type, or Noetherianity is needed here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

universe u

/-- A nonsurjective closed immersion into an integral scheme lowers a finite
topological dimension bound by one. -/
theorem Hom.topologicalKrullDim_le_of_isClosedImmersion_of_not_surjective
    {Z X : Scheme.{u}} [IsIntegral X] (i : Z ⟶ X) [IsClosedImmersion i]
    (hi : ¬ Function.Surjective i) (d : ℕ)
    (hdim : topologicalKrullDim X ≤ (d + 1 : ℕ)) :
    topologicalKrullDim Z ≤ (d : ℕ) := by
  have hclosed : IsClosed (Set.range i) := i.isClosedEmbedding.isClosed_range
  have hgeneric : genericPoint X ∉ Set.range i := by
    intro h
    apply hi
    have hcl := closure_minimal (Set.singleton_subset_iff.mpr h) hclosed
    rw [genericPoint_closure] at hcl
    exact fun x => hcl (Set.mem_univ x)
  have havoid : Disjoint (Set.range i) (genericPoints X) := by
    rw [genericPoints_eq_singleton, Set.disjoint_singleton_right]
    exact hgeneric
  calc
    topologicalKrullDim Z = topologicalKrullDim (Set.range i) :=
      IsHomeomorph.topologicalKrullDim_eq _
        i.isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph
    _ ≤ (d : ℕ) := topologicalKrullDim_closed_le_of_avoids_genericPoints
      (Set.range i) hclosed havoid d hdim

/-- The literal fibre of a surjective map from an integral scheme over a
closed field-valued point of a nontrivial target lowers dimension by one. -/
theorem Hom.topologicalKrullDim_closedPointFiber_le
    {X T : Scheme.{u}} [IsIntegral X] [Nontrivial T]
    (g : X ⟶ T) [Surjective g]
    (K : Type u) [Field K] (η : Spec (.of K) ⟶ T) [IsClosedImmersion η]
    (d : ℕ) (hdim : topologicalKrullDim X ≤ (d + 1 : ℕ)) :
    topologicalKrullDim (pullback (C := Scheme) g η) ≤ (d : ℕ) := by
  apply (pullback.fst g η).topologicalKrullDim_le_of_isClosedImmersion_of_not_surjective
    (d := d) (hdim := hdim)
  intro hf
  have hη : Function.Surjective η := by
    intro t
    obtain ⟨x, rfl⟩ := g.surjective t
    obtain ⟨z, rfl⟩ := hf x
    refine ⟨pullback.snd g η z, ?_⟩
    exact congrArg (fun h : pullback g η ⟶ T => h z) (pullback.condition (f := g) (g := η)).symm
  exact not_subsingleton T hη.subsingleton

end AlgebraicGeometry.Scheme
