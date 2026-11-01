/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.Sober

/-!
# Generic codimension of a proper closed image

If an irreducible closed subspace has dimension n and the irreducible ambient
space has dimension at most n+1, its generic point has coheight one. The proof
concatenates specialization chains, through the native height-plus-coheight
bound. No catenarity, regularity or Noetherianity hypothesis is needed.
-/

@[expose] public noncomputable section

open Order TopologicalSpace Topology

attribute [local instance] specializationOrder

namespace TopologicalSpace

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [QuasiSober X] [T0Space X] [IrreducibleSpace X]
  [QuasiSober Y] [T0Space Y] [IrreducibleSpace Y]

/-- A proper closed image of dimension n in an irreducible ambient space
of dimension at most n+1 has generic codimension exactly one. -/
theorem coheight_image_genericPoint_eq_one (f : X → Y) (hf : IsClosedEmbedding f)
    (n : ℕ) (hX : topologicalKrullDim X = n)
    (hY : topologicalKrullDim Y ≤ (n : WithBot ℕ∞) + 1)
    (hrange : Set.range f ≠ Set.univ) : Order.coheight (f (genericPoint X)) = 1 := by
  let : OrderTop X := { top := genericPoint X, le_top := genericPoint_specializes }
  let : OrderTop Y := { top := genericPoint Y, le_top := genericPoint_specializes }
  have hX' : Order.krullDim X = (n : WithBot ℕ∞) := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))]
    exact hX
  have hY' : Order.krullDim Y ≤ (n : WithBot ℕ∞) + 1 := by
    rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Y))]
    exact hY
  have hheightX : (Order.height (genericPoint X) : WithBot ℕ∞) = n :=
    (Order.height_top_eq_krullDim (α := X)).trans hX'
  have hheightX' : Order.height (genericPoint X) = (n : ℕ∞) := by exact_mod_cast hheightX
  have hmono : StrictMono f :=
    hf.continuous.specialization_monotone.strictMono_of_injective hf.injective
  have hheight : (n : ℕ∞) ≤ Order.height (f (genericPoint X)) := by
    simpa only [hheightX'] using
      Order.height_le_height_apply_of_strictMono f hmono (genericPoint X)
  have hsum : ((Order.height (f (genericPoint X)) +
      Order.coheight (f (genericPoint X)) : ℕ∞) : WithBot ℕ∞) ≤ Order.krullDim Y := by
    rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
    exact_mod_cast le_iSup
      (fun y : Y => Order.height y + Order.coheight y) (f (genericPoint X))
  have hsum' : Order.height (f (genericPoint X)) + Order.coheight (f (genericPoint X)) ≤
      (n : ℕ∞) + 1 := by exact_mod_cast hsum.trans hY'
  have hle : Order.coheight (f (genericPoint X)) ≤ 1 :=
    (ENat.add_le_add_iff_left (by simp : (n : ℕ∞) ≠ ⊤)).mp
      ((add_le_add hheight (le_refl (Order.coheight (f (genericPoint X))))).trans hsum')
  have hne : f (genericPoint X) ≠ genericPoint Y := by
    intro heq
    have hsub : closure ({genericPoint Y} : Set Y) ⊆ Set.range f :=
      hf.isClosed_range.closure_subset_iff.mpr
        (Set.singleton_subset_iff.mpr (heq ▸ Set.mem_range_self (genericPoint X)))
    rw [genericPoint_closure] at hsub
    exact hrange (Set.eq_univ_of_univ_subset hsub)
  have hlt : f (genericPoint X) < (⊤ : Y) :=
    lt_of_le_of_ne le_top hne
  have hge : 1 ≤ Order.coheight (f (genericPoint X)) :=
    Order.one_le_iff_ne_zero.mpr (Order.coheight_pos_of_lt_top hlt).ne'
  exact le_antisymm hle hge

end TopologicalSpace
