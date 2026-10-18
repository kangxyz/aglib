/-
Copyright (c) 2026 Motivic Cohomology contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.PGroupNormalSubfield

/-!
# A normal prime subfield of the original embedded field

The input field is not replaced by its range in a finite Galois ambient
extension. The actual fixed-field construction is transported back along
the native equivalence with that range.
-/

@[expose] public noncomputable section

namespace IntermediateField

variable {k H Ω : Type*} [Field k] [Field H] [Field Ω]
  [Algebra k H] [Algebra k Ω] [FiniteDimensional k H]
  [FiniteDimensional k Ω] [IsGalois k Ω]

/-- A nontrivial finite field embedded in a finite Galois p-group extension
contains an actual normal degree-p subfield, with strictly smaller upper degree. -/
theorem exists_normal_prime_subfield_of_embedding (p : ℕ) [Fact p.Prime]
    (hG : IsPGroup p (Ω ≃ₐ[k] Ω)) (g : H →ₐ[k] Ω)
    (hH : 1 < Module.finrank k H) :
    ∃ L : IntermediateField k H, Normal k L ∧ Module.finrank k L = p ∧
      Module.finrank L H < Module.finrank k H := by
  have hrange : g.fieldRange ≠ ⊥ := by
    intro h
    have hdegree := g.equivFieldRange.toLinearEquiv.finrank_eq
    rw [h, IntermediateField.finrank_bot] at hdegree
    exact (Nat.ne_of_gt hH) hdegree
  obtain ⟨L₀, hnormal, hdegree, _⟩ :=
    exists_normal_prime_subfield_of_isPGroup p hG g.fieldRange hrange
  let L : IntermediateField k H := L₀.map g.equivFieldRange.symm.toAlgHom
  let ε : L₀ ≃ₐ[k] L := equivMap L₀ g.equivFieldRange.symm.toAlgHom
  let : Normal k L₀ := hnormal
  have hLnormal : Normal k L := Normal.of_algEquiv ε
  have hLdegree : Module.finrank k L = p := ε.toLinearEquiv.finrank_eq.symm.trans hdegree
  refine ⟨L, hLnormal, hLdegree, ?_⟩
  rw [← Module.finrank_mul_finrank k L H, hLdegree]
  exact lt_mul_of_one_lt_left Module.finrank_pos (Fact.out : p.Prime).one_lt

end IntermediateField
