/-
Copyright (c) 2026 algebraic-geometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.DirectSum.Module

/-! # The direct sum of original kernels is the kernel of the original direct-sum map -/

@[expose] public noncomputable section
namespace DirectSum
universe u v w z
variable {R : Type u} [Ring R] {ι : Type v}
  {M : ι → Type w} {N : ι → Type z}
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
  [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  (f : ∀ i, M i →ₗ[R] N i)

/-- The native componentwise inclusion has precisely the original direct-sum kernel as range. -/
theorem range_lmap_kernel_subtype :
    (lmap (fun i => (f i).ker.subtype)).range = (lmap f).ker := by
  rw [range_lmap, ker_lmap]
  simp only [Submodule.range_subtype]

/-- The original componentwise kernel inclusion, with its actual codomain restricted. -/
def kernelLmapInclusion : (⨁ i, (f i).ker) →ₗ[R] (lmap f).ker :=
  (lmap (fun i => (f i).ker.subtype)).codRestrict (lmap f).ker fun x => by
    rw [← range_lmap_kernel_subtype f]
    exact LinearMap.mem_range_self _ x

/-- Direct sums commute with these original kernels, retaining the original inclusion. -/
def kernelLmapEquiv : (⨁ i, (f i).ker) ≃ₗ[R] (lmap f).ker :=
  LinearEquiv.ofBijective (kernelLmapInclusion f) ⟨by
    intro x y h
    apply (lmap_injective (fun i => (f i).ker.subtype)).mpr
      (fun _ => Subtype.val_injective)
    exact congrArg Subtype.val h, by
    intro y
    have hy : (y : ⨁ i, M i) ∈ (lmap (fun i => (f i).ker.subtype)).range := by
      rw [range_lmap_kernel_subtype]
      exact y.property
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩⟩

@[simp]
theorem kernelLmapEquiv_apply (x : ⨁ i, (f i).ker) :
    (kernelLmapEquiv f x : ⨁ i, M i) = lmap (fun i => (f i).ker.subtype) x := rfl

@[simp]
theorem kernelLmapEquiv_apply_component (x : ⨁ i, (f i).ker) (i : ι) :
    (kernelLmapEquiv f x : ⨁ i, M i) i = x i := rfl

end DirectSum
