/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.Exact.Basic

/-!
# Right exact diagrams of original linear maps

In a commuting diagram with right exact rows, surjectivity of the first vertical map and
bijectivity of the second imply bijectivity of the third. The proof uses the original
maps and exactness predicates directly, preserving independent universes for all six
module carriers and the scalar ring.
-/

@[expose] public section

universe u v₁ v₂ v₃ w₁ w₂ w₃

namespace LinearMap

variable {R : Type u} [Ring R]
  {M₁ : Type v₁} {M₂ : Type v₂} {M₃ : Type v₃}
  {N₁ : Type w₁} {N₂ : Type w₂} {N₃ : Type w₃}
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
  [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃]
  [Module R M₁] [Module R M₂] [Module R M₃]
  [Module R N₁] [Module R N₂] [Module R N₃]

/-- The original last vertical map in a right exact linear diagram is bijective when the
first is surjective and the middle is bijective. All carrier universes are independent. -/
theorem bijective_of_rightExact_diagram
    (f₁ : M₁ →ₗ[R] M₂) (g₁ : M₂ →ₗ[R] M₃)
    (f₂ : N₁ →ₗ[R] N₂) (g₂ : N₂ →ₗ[R] N₃)
    (p₁ : M₁ →ₗ[R] N₁) (p₂ : M₂ →ₗ[R] N₂) (p₃ : M₃ →ₗ[R] N₃)
    (h₁ : Function.Exact f₁ g₁) (h₂ : Function.Exact f₂ g₂)
    (hg₁ : Function.Surjective g₁) (hg₂ : Function.Surjective g₂)
    (hcomm₁ : p₂.comp f₁ = f₂.comp p₁) (hcomm₂ : p₃.comp g₁ = g₂.comp p₂)
    (hp₁ : Function.Surjective p₁) (hp₂ : Function.Bijective p₂) :
    Function.Bijective p₃ := by
  constructor
  · apply (injective_iff_map_eq_zero p₃).mpr
    intro x hx
    obtain ⟨y, rfl⟩ := hg₁ x
    have hy : g₂ (p₂ y) = 0 := (DFunLike.congr_fun hcomm₂ y).symm.trans hx
    obtain ⟨z, hz⟩ := (h₂ (p₂ y)).mp hy
    obtain ⟨a, ha⟩ := hp₁ z
    have hay : f₁ a = y := hp₂.injective
      ((DFunLike.congr_fun hcomm₁ a).trans (by rw [LinearMap.comp_apply, ha]; exact hz))
    rw [← hay]
    exact h₁.apply_apply_eq_zero a
  · intro x
    obtain ⟨y, hy⟩ := hg₂ x
    obtain ⟨z, hz⟩ := hp₂.surjective y
    exact ⟨g₁ z, (DFunLike.congr_fun hcomm₂ z).trans (by rw [LinearMap.comp_apply, hz]; exact hy)⟩

end LinearMap
