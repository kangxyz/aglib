/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.LinearAlgebra.KernelFiltration

/-! # Kernel-filtration maps with the original composite retained -/

@[expose] public noncomputable section
namespace LinearMap
universe u v w z
variable {R : Type u} [Ring R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]
  {P : Type z} [AddCommGroup P] [Module R P]
  (f : M →ₗ[R] N) (g : N →ₗ[R] P) (k : M →ₗ[R] P) (w : g.comp f = k)

/-- The original map restricted to the kernel of its original composite. -/
def kernelFiltrationMap : k.ker →ₗ[R] g.ker where
  toFun x := ⟨f x, by change (g.comp f) x = 0; rw [w]; exact x.property⟩
  map_add' x y := by apply Subtype.ext; exact f.map_add x y
  map_smul' a x := by apply Subtype.ext; exact f.map_smul a x

@[simp]
theorem kernelFiltrationMap_apply (x : k.ker) :
    (kernelFiltrationMap f g k w x : N) = f x := rfl

@[simp]
theorem ker_kernelFiltrationMap :
    (kernelFiltrationMap f g k w).ker = f.ker.comap k.ker.subtype := by
  ext x
  change (kernelFiltrationMap f g k w x = 0) ↔ f x = 0
  exact Subtype.ext_iff

theorem kernelFiltrationMap_surjective (hf : Function.Surjective f) :
    Function.Surjective (kernelFiltrationMap f g k w) := by
  intro x
  obtain ⟨y, hy⟩ := hf x
  refine ⟨⟨y, ?_⟩, Subtype.ext hy⟩
  change k y = 0
  rw [← w, LinearMap.comp_apply, hy]
  exact x.property

end LinearMap
