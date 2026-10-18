/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.AdjoinRootScalarBranches
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.Sylow

/-!
# Actual branch embeddings into a specified splitting field

Each irreducible branch after coefficient extension has a root in a specified
overfield where the original polynomial splits. Its literal quotient field
therefore embeds into that overfield. The branch degree never increases.
For a Sylow fixed field, the relative ambient automorphism group is the
original Sylow subgroup under the native Galois correspondence equivalence.
-/

@[expose] public noncomputable section

open Polynomial

namespace AdjoinRoot

variable {k L Ω : Type*} [Field k] [Field L] [Field Ω]
  [Algebra k L] [Algebra k Ω] [Algebra L Ω] [IsScalarTower k L Ω]

/-- Every literal scalar branch embeds over the coefficient field in the
specified splitting overfield; its degree is bounded by the original degree. -/
theorem nonempty_algHom_branch_of_splits (p : k[X]) (hp : p ≠ 0)
    (hsplit : (p.map (algebraMap k Ω)).Splits)
    (q : IrreducibleBranch (p.map (algebraMap k L))) :
    Nonempty (AdjoinRoot q.val.val →ₐ[L] Ω) ∧ q.val.val.natDegree ≤ p.natDegree := by
  have hsplitL : ((p.map (algebraMap k L)).map (algebraMap L Ω)).Splits := by
    simpa only [Polynomial.map_map, ← IsScalarTower.algebraMap_eq] using hsplit
  have hqsplit : (q.val.val.map (algebraMap L Ω)).Splits :=
    hsplitL.of_dvd (Polynomial.map_ne_zero (Polynomial.map_ne_zero hp))
      (Polynomial.map_dvd (algebraMap L Ω) q.property)
  have hqdegree : (q.val.val.map (algebraMap L Ω)).degree ≠ 0 := by
    apply degree_ne_of_natDegree_ne
    rw [natDegree_map]
    exact Nat.ne_of_gt q.val.property.2.natDegree_pos
  obtain ⟨a, ha⟩ := hqsplit.exists_eval_eq_zero hqdegree
  have hroot : aeval a q.val.val = 0 := by
    simpa only [eval_map, aeval_def] using ha
  refine ⟨⟨AdjoinRoot.liftAlgHom q.val.val (Algebra.ofId L Ω) a hroot⟩, ?_⟩
  simpa only [natDegree_map] using
    natDegree_le_of_dvd q.property (Polynomial.map_ne_zero hp)

end AdjoinRoot

namespace IntermediateField

variable {k Ω : Type*} [Field k] [Field Ω] [Algebra k Ω] [FiniteDimensional k Ω]

/-- The actual automorphism group above a Sylow fixed field is a group of
the same prime-power type as the specified Sylow subgroup. -/
theorem isPGroup_aut_over_sylow_fixedField (p : ℕ) (S : Sylow p (Ω ≃ₐ[k] Ω)) :
    IsPGroup p (Ω ≃ₐ[fixedField (S : Subgroup (Ω ≃ₐ[k] Ω))] Ω) :=
  S.isPGroup'.of_equiv (subgroupEquivAlgEquiv (S : Subgroup (Ω ≃ₐ[k] Ω)))

end IntermediateField
