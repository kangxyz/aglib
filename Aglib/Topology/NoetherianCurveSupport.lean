/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Topology.KrullDimension
public import Mathlib.Topology.NoetherianSpace

/-!
# Finite closed support away from generic points on a Noetherian curve

Only topological dimension, sobriety and Noetherianity enter. This applies to
actual quasi-compact curve tests, without reducedness or smoothness, and makes
no finite-support assertion for arbitrary non-quasi-compact etale tests.
-/

@[expose] public noncomputable section

open Set TopologicalSpace Order

namespace TopologicalSpace

universe u

variable {X : Type u} [TopologicalSpace X] [T0Space X]

omit [T0Space X] in
private theorem mem_genericPoints_of_isMax_closure (x : X)
    (hx : IsMax (⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩ :
      IrreducibleCloseds X)) : x ∈ genericPoints X := by
  change closure {x} ∈ irreducibleComponents X
  rw [irreducibleComponents_eq_maximals_closed]
  refine ⟨⟨isClosed_closure, isIrreducible_singleton.closure⟩, ?_⟩
  intro t ht hxt
  exact hx (show (⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩ :
    IrreducibleCloseds X) ≤ ⟨t, ht.2, ht.1⟩ from hxt)

/-- Every nongeneric point of a space of dimension at most one is closed. -/
theorem isClosed_singleton_of_not_generic_of_dim_le_one
    (hdim : topologicalKrullDim X ≤ 1) {x : X} (hx : x ∉ genericPoints X) :
    IsClosed ({x} : Set X) := by
  have hmin : IsMin (⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩ :
      IrreducibleCloseds X) :=
    ((krullDim_le_one_iff.mp hdim) _).resolve_right
      (fun h => hx (mem_genericPoints_of_isMax_closure x h))
  apply closure_subset_iff_isClosed.mp
  intro y hy
  have hyx : closure ({y} : Set X) ⊆ closure {x} :=
    closure_minimal (singleton_subset_iff.mpr hy) isClosed_closure
  have hxy : closure ({x} : Set X) ⊆ closure {y} :=
    hmin (show (⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩ :
      IrreducibleCloseds X) ≤ ⟨closure {x}, isIrreducible_singleton.closure,
        isClosed_closure⟩ from hyx)
  exact (IsGenericPoint.eq (show IsGenericPoint y (closure {x}) from hyx.antisymm hxy)
    isGenericPoint_closure)

/-- A closed subset avoiding the generic points of a Noetherian sober curve is finite. -/
theorem finite_closed_of_disjoint_genericPoints [QuasiSober X] [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ 1) {Z : Set X} (hZ : IsClosed Z)
    (hgeneric : ∀ x ∈ Z, x ∉ genericPoints X) : Z.Finite := by
  obtain ⟨S, hS, hclosed, hirred, hcover⟩ :=
    NoetherianSpace.exists_finite_set_isClosed_irreducible hZ
  rw [hcover]
  apply hS.sUnion
  intro t ht
  let x := (hirred t ht).genericPoint
  have hx : IsGenericPoint x t := (hirred t ht).isGenericPoint_genericPoint (hclosed t ht)
  have hxZ : x ∈ Z := by
    rw [hcover]
    exact mem_sUnion_of_mem hx.mem ht
  have hpoint := isClosed_singleton_of_not_generic_of_dim_le_one hdim (hgeneric x hxZ)
  rw [← hx.def, hpoint.closure_eq]
  exact finite_singleton x

/-- The complement of an open containing all generic points is finite on a Noetherian curve. -/
theorem finite_compl_open_of_contains_genericPoints [QuasiSober X] [NoetherianSpace X]
    (hdim : topologicalKrullDim X ≤ 1) {U : Set X} (hU : IsOpen U)
    (hgeneric : genericPoints X ⊆ U) : Uᶜ.Finite :=
  finite_closed_of_disjoint_genericPoints hdim hU.isClosed_compl
    (fun _ hx hg => hx (hgeneric hg))

end TopologicalSpace
