/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.Constructible
public import Mathlib.Topology.Sober

/-! # Constructible membership near a generic point

The existing Boolean induction for constructible subsets supplies an actual
open neighbourhood where membership agrees with membership at the generic
point. No Noetherian or scheme hypothesis is needed.
-/

@[expose] public section

open Set TopologicalSpace Topology

namespace IsGenericPoint

variable {X : Type*} [TopologicalSpace X] {η : X}

/-- Constructible membership is constant on an actual neighbourhood of a
point generic for the whole space. -/
theorem exists_open_membership_iff (hη : IsGenericPoint η (Set.univ : Set X))
    {s : Set X} (hs : IsConstructible s) :
    ∃ U : Set X, IsOpen U ∧ η ∈ U ∧ ∀ x ∈ U, (x ∈ s ↔ η ∈ s) := by
  classical
  induction hs using IsConstructible.empty_union_induction with
  | open_retrocompact V hV _ =>
      by_cases hv : η ∈ V
      · exact ⟨V, hV, hv, fun x hx => ⟨fun _ => hv, fun _ => hx⟩⟩
      · refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, fun x _ => ?_⟩
        constructor
        · intro hx
          exact (hv ((hη.mem_open_set_iff hV).mpr ⟨x, Set.mem_univ _, hx⟩)).elim
        · exact fun h => (hv h).elim
  | union s hs t ht ihs iht =>
      obtain ⟨U, hU, hηU, hUs⟩ := ihs
      obtain ⟨V, hV, hηV, hVt⟩ := iht
      refine ⟨U ∩ V, hU.inter hV, ⟨hηU, hηV⟩, fun x hx => ?_⟩
      exact or_congr (hUs x hx.1) (hVt x hx.2)
  | compl s hs ih =>
      obtain ⟨U, hU, hηU, hUs⟩ := ih
      exact ⟨U, hU, hηU, fun x hx => not_congr (hUs x hx)⟩

/-- A constructible subset missing the generic point misses an actual open
neighbourhood of it. -/
theorem exists_open_disjoint_of_isConstructible
    (hη : IsGenericPoint η (Set.univ : Set X)) {s : Set X}
    (hs : IsConstructible s) (hηs : η ∉ s) :
    ∃ U : Set X, IsOpen U ∧ η ∈ U ∧ Disjoint U s := by
  obtain ⟨U, hU, hηU, hUs⟩ := hη.exists_open_membership_iff hs
  exact ⟨U, hU, hηU, Set.disjoint_left.mpr fun x hx hxs => hηs ((hUs x hx).mp hxs)⟩

end IsGenericPoint
