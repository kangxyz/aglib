/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Sober
public import Mathlib.Data.Set.Card

/-!
# Irreducible components from closed irredundant covers


Source: `R5Lab.Aglib.Topology.Irreducible.ClosedCover`.
Packet SHA-256:
`da768716adbf6079dd77fd7f5a7deb12e909f79dc8c15d2811ce0c83abbcc55f`.
Actual hypotheses, universes and forward maps are retained; source identity is
separate from compilation and mathematical-adoption evidence.
-/

@[expose] public section

noncomputable section
open Set
universe u v


section Topology
variable {X : Type u} [TopologicalSpace X] [QuasiSober X] {ι : Type v}

/-- In a sober space, an irredundant closed irreducible cover is the actual
component family. This derives the inventory from actual images. -/
theorem irreducibleComponents_eq_range (s : ι → Set X)
    (hc : ∀ i, IsClosed (s i)) (hi : ∀ i, IsIrreducible (s i))
    (cover : ∀ x, ∃ i, x ∈ s i) (hn : ∀ i j, s i ⊆ s j → i = j) :
    irreducibleComponents X = Set.range s := by
  have inside (z : Set X) (hz : IsIrreducible z) : ∃ i, z ⊆ s i := by
    obtain ⟨i, hp⟩ := cover hz.genericPoint
    refine ⟨i, subset_closure.trans ?_⟩
    rw [← hz.genericPoint_closure_eq]
    exact (hc i).closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hp)
  have member (i : ι) : s i ∈ irreducibleComponents X := by
    refine ⟨hi i, ?_⟩
    intro z hz hiz
    obtain ⟨j, hj⟩ := inside z hz
    have e := hn i j (hiz.trans hj)
    simpa only [← e] using hj
  ext z
  constructor
  · intro hz
    obtain ⟨i, hi'⟩ := inside z hz.1
    exact ⟨i, (Subset.antisymm hi' (hz.2 (hi i) hi')).symm⟩
  · rintro ⟨i, rfl⟩
    exact member i
end Topology


variable {X : Type u} [TopologicalSpace X]

/-- A two-member closed irreducible cover with neither member contained in the
other is exactly the actual set of irreducible components. -/
theorem irreducibleComponents_eq_pair {s t : Set X}
    (hs : IsClosed s) (ht : IsClosed t) (his : IsIrreducible s) (hit : IsIrreducible t)
    (cover : s ∪ t = univ) (hst : ¬s ⊆ t) (hts : ¬t ⊆ s) :
    irreducibleComponents X = {s, t} := by
  have cases' (z : Set X) (hz : IsIrreducible z) : z ⊆ s ∨ z ⊆ t :=
    (isPreirreducible_iff_isClosed_union_isClosed.mp hz.2) s t hs ht (by
      rw [cover]
      exact subset_univ _)
  have hs' : s ∈ irreducibleComponents X := by
    refine ⟨his, ?_⟩
    intro z hz hsz
    rcases cases' z hz with hzs | hzt
    · exact hzs
    · exact (hst (hsz.trans hzt)).elim
  have ht' : t ∈ irreducibleComponents X := by
    refine ⟨hit, ?_⟩
    intro z hz htz
    rcases cases' z hz with hzs | hzt
    · exact (hts (htz.trans hzs)).elim
    · exact hzt
  ext z
  constructor
  · intro hz
    rcases cases' z hz.1 with hzs | hzt
    · exact mem_insert_iff.mpr (Or.inl (Subset.antisymm hzs (hz.2 his hzs)))
    · exact mem_insert_iff.mpr (Or.inr (mem_singleton_iff.mpr (Subset.antisymm hzt (hz.2 hit hzt))))
  · rintro (rfl | rfl) <;> assumption

theorem irreducibleComponents_card_two {s t : Set X}
    (hs : IsClosed s) (ht : IsClosed t) (his : IsIrreducible s) (hit : IsIrreducible t)
    (cover : s ∪ t = univ) (hst : ¬s ⊆ t) (hts : ¬t ⊆ s) :
    Nat.card (irreducibleComponents X) = 2 := by
  change (irreducibleComponents X).ncard = 2
  rw [irreducibleComponents_eq_pair hs ht his hit cover hst hts]
  exact ncard_pair (fun h => hst (h ▸ subset_refl _))
