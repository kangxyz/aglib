/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.FieldTheory.KummerSubextension

/-! # The original generator of an embedded Kummer subextension

Literal power recognition is transported back through the given embedding.
The returned generator belongs to the original field, and its image is the
specified power of the unchanged ambient root. No replacement field or
arbitrary Kummer radicand is selected.
-/

@[expose] public noncomputable section

open Polynomial IntermediateField

namespace AlgHom

universe u v w

variable {K : Type u} {F : Type v} {L : Type w}
  [Field K] [Field F] [Field L] [Algebra K F] [Algebra K L]

/-- An original field embedded in the specified Kummer extension has a root
generator whose image is the exact required power of the original root.
Its original degree is positive and divides the original root order. -/
theorem exists_root_generator_of_kummer_embedding
    (i : L →ₐ[K] F) {N : ℕ} (hN : 0 < N) {a : K} {θ : F}
    (hθ : θ ^ N = algebraMap K F a) (hgen : K⟮θ⟯ = ⊤)
    (hirr : Irreducible (X ^ N - C a)) (hroots : (primitiveRoots N K).Nonempty) :
    ∃ (e : ℕ) (β : L), 0 < e ∧ e ∣ N ∧ Module.finrank K L = e ∧
      β ^ e = algebraMap K L a ∧ K⟮β⟯ = ⊤ ∧ i β = θ ^ (N / e) := by
  obtain ⟨he, heN, hE⟩ :=
    IntermediateField.eq_adjoin_pow_of_kummer hN hθ hgen hirr hroots i.fieldRange
  let e := Module.finrank K i.fieldRange
  have hmem : θ ^ (N / e) ∈ i.fieldRange := by
    rw [hE]
    exact IntermediateField.mem_adjoin_simple_self K _
  obtain ⟨β, hβ⟩ := hmem
  have hβ' : i β = θ ^ (N / e) := hβ
  refine ⟨e, β, he, heN, i.equivFieldRange.toLinearEquiv.finrank_eq, ?_, ?_, hβ⟩
  · apply i.injective
    rw [map_pow, hβ, ← pow_mul, Nat.div_mul_cancel heN, hθ]
    exact (i.commutes a).symm
  · apply IntermediateField.map_injective i
    rw [IntermediateField.adjoin_map, Set.image_singleton, hβ', ← hE,
      ← AlgHom.fieldRange_eq_map]

end AlgHom
