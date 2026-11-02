/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-! # The third actual arrow in a morphism of short exact sequences -/
@[expose] public noncomputable section
namespace CategoryTheory.ShortComplex
open Limits
variable {C : Type*} [Category* C] [Preadditive C] [Balanced C]

/-- If the first two comparison arrows are isomorphisms, so is the original third arrow. -/
theorem isIso₃_of_shortExact_of_isIso₁₂ {S T : ShortComplex C} (φ : S ⟶ T)
    (hS : S.ShortExact) (hT : T.ShortExact) [IsIso φ.τ₁] [IsIso φ.τ₂] : IsIso φ.τ₃ := by
  let := hS.epi_g
  let := hT.epi_g
  have hz : T.f ≫ (inv φ.τ₂ ≫ S.g) = 0 := by
    apply (cancel_epi φ.τ₁).mp
    rw [comp_zero, ← Category.assoc φ.τ₁, φ.comm₁₂, Category.assoc,
      IsIso.hom_inv_id_assoc, S.zero]
  let ψ := hT.exact.desc (inv φ.τ₂ ≫ S.g) hz
  have hψ : T.g ≫ ψ = inv φ.τ₂ ≫ S.g := hT.exact.g_desc _ hz
  refine ⟨⟨ψ, ?_, ?_⟩⟩
  · apply (cancel_epi S.g).mp
    rw [← Category.assoc, ← φ.comm₂₃, Category.assoc, hψ,
      IsIso.hom_inv_id_assoc, Category.comp_id]
  · apply (cancel_epi T.g).mp
    rw [← Category.assoc, hψ, Category.assoc, ← φ.comm₂₃,
      IsIso.inv_hom_id_assoc, Category.comp_id]
end CategoryTheory.ShortComplex
