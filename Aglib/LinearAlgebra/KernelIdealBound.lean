/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-! # Original kernel-ideal bounds under linear change of coordinates -/

@[expose] public noncomputable section
namespace LinearMap
universe u v w x y
variable {R : Type u} [CommRing R]
  {M : Type v} {N : Type w} {M' : Type x} {N' : Type y}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']
  [Module R M] [Module R N] [Module R M'] [Module R N']

/-- An original commuting square of linear equivalences transports an actual
kernel containment in the ideal multiple, preserving the original ideal. -/
theorem ker_le_smul_top_of_equiv (I : Ideal R) (f : M →ₗ[R] N) (g : M' →ₗ[R] N')
    (e : M ≃ₗ[R] M') (d : N ≃ₗ[R] N')
    (w : ∀ x, d (f x) = g (e x))
    (hg : g.ker ≤ I • (⊤ : Submodule R M')) :
    f.ker ≤ I • (⊤ : Submodule R M) := by
  intro x hx
  change f x = 0 at hx
  have hy : e x ∈ g.ker := by
    change g (e x) = 0
    rw [← w, hx, map_zero]
  have hz := Submodule.mem_map_of_mem (f := e.symm.toLinearMap) (hg hy)
  rw [Submodule.map_smul'', Submodule.map_top,
    LinearMap.range_eq_top.mpr e.symm.surjective] at hz
  simpa using hz

end LinearMap
