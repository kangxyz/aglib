/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.Isomorphisms

/-! # Original successive quotients in a filtration by transition kernels -/

@[expose] public noncomputable section

namespace LinearMap

universe u v w z

variable {R : Type u} [Ring R]
  {M : Type v} [AddCommGroup M] [Module R M]
  {N : Type w} [AddCommGroup N] [Module R N]
  {P : Type z} [AddCommGroup P] [Module R P]
  (f : M →ₗ[R] N) (g : N →ₗ[R] P)

/-- The original first map sends the kernel of the composite into the kernel
of the second map. For tower reductions this is the actual filtration-piece
map, without a cartesian or ideal-adic hypothesis. -/
def compKernelMap : (g.comp f).ker →ₗ[R] g.ker where
  toFun x := ⟨f x, x.property⟩
  map_add' x y := by apply Subtype.ext; exact f.map_add x y
  map_smul' a x := by apply Subtype.ext; exact f.map_smul a x

@[simp]
theorem compKernelMap_apply (x : (g.comp f).ker) :
    (compKernelMap f g x : N) = f x := rfl

/-- The kernel is the original next filtration term inside the current one. -/
theorem ker_compKernelMap :
    (compKernelMap f g).ker = f.ker.comap (g.comp f).ker.subtype := by
  ext x
  change (compKernelMap f g x = 0) ↔ f x = 0
  exact Subtype.ext_iff

/-- Surjectivity of the original transition gives surjectivity on the actual
successive filtration piece. -/
theorem compKernelMap_surjective (hf : Function.Surjective f) :
    Function.Surjective (compKernelMap f g) := by
  intro x
  obtain ⟨y, hy⟩ := hf x
  have hgy : y ∈ (g.comp f).ker := by
    change g (f y) = 0
    rw [hy]
    exact x.property
  exact ⟨⟨y, hgy⟩, Subtype.ext hy⟩

/-- The original quotient of consecutive transition kernels is canonically
the original adjacent transition kernel. -/
def compKernelQuotientEquiv (hf : Function.Surjective f) :
    ((g.comp f).ker ⧸ f.ker.comap (g.comp f).ker.subtype) ≃ₗ[R] g.ker :=
  (Submodule.quotEquivOfEq _ _ (ker_compKernelMap f g).symm).trans
    ((compKernelMap f g).quotKerEquivOfSurjective (compKernelMap_surjective f g hf))

@[simp]
theorem compKernelQuotientEquiv_mk (hf : Function.Surjective f) (x : (g.comp f).ker) :
    (compKernelQuotientEquiv f g hf (Submodule.Quotient.mk x) : N) = f x := by
  simp [compKernelQuotientEquiv]

end LinearMap
