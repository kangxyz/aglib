/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteStratification.ClosedComplement

/-! # Composing actual finite locally closed partitions

The refining strata are the original schemes, with their original composite
immersions. No coefficient, sheaf category or derived realization is chosen.
Noetherianity supplies constructibility of the composite immersion ranges.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteLocallyClosedPartition

universe u

/-- Compose an actual partition with actual partitions of its strata. -/
def compose {X : Scheme.{u}} [IsNoetherian X]
    (p : FiniteLocallyClosedPartition X)
    (q : ∀ i, FiniteLocallyClosedPartition (p.stratum i)) :
    FiniteLocallyClosedPartition X := by
  classical
  let S (ij : Σ i, Fin (q i).count) := (q ij.1).stratum ij.2
  let f (ij : Σ i, Fin (q i).count) : S ij ⟶ X :=
    (q ij.1).inclusion ij.2 ≫ p.inclusion ij.1
  have hf (ij) : IsImmersion (f ij) := by
    have := p.immersion ij.1
    have := (q ij.1).immersion ij.2
    exact inferInstanceAs (IsImmersion ((q ij.1).inclusion ij.2 ≫ p.inclusion ij.1))
  have hc (ij) : Topology.IsConstructible (Set.range (f ij)) := by
    have := hf ij
    exact isConstructible_range_of_noetherian (f ij)
  have hd : Pairwise fun ij kl => Disjoint (Set.range (f ij)) (Set.range (f kl)) := by
    rintro ⟨i, j⟩ ⟨k, l⟩ hne
    apply Set.disjoint_left.mpr
    rintro x ⟨y, rfl⟩ ⟨z, hz⟩
    by_cases hik : i = k
    · subst k
      have := p.immersion i
      have heq : (q i).inclusion l z = (q i).inclusion j y :=
        (p.inclusion i).isEmbedding.injective hz
      have hjl : j ≠ l := by
        intro h
        subst l
        exact hne rfl
      exact Set.disjoint_left.mp ((q i).disjoint hjl) ⟨y, rfl⟩ ⟨z, heq⟩
    · exact Set.disjoint_left.mp (p.disjoint hik)
        ⟨(q i).inclusion j y, rfl⟩ ⟨(q k).inclusion l z, hz⟩
  have hcover : ∀ x : X, ∃ ij, ∃ y : S ij, f ij y = x := by
    intro x
    obtain ⟨i, y, hy⟩ := p.covers x
    obtain ⟨j, z, hz⟩ := (q i).covers y
    exact ⟨⟨i, j⟩, z, (congrArg (p.inclusion i) hz).trans hy⟩
  exact FiniteLocallyClosedPartition.ofFintype S f hf hc hd hcover

end AlgebraicGeometry.Scheme.EtaleCohomology.Constructible.FiniteLocallyClosedPartition
