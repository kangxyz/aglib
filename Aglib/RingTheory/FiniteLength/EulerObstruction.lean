/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Length
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Finite-length Euler obstruction to a tensor kernel

The kernel and image of an actual linear map give an additive Euler identity.
Finite cancellation then detects injectivity after tensoring a presentation.
The numerical relation between the two basis cardinalities is an explicit
hypothesis, independent of how a consumer proves its rank formula.
-/

@[expose] public section

namespace LinearMap

variable {R : Type*} {M : Type*} {N : Type*} {P : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- The Euler identity for a right exact pair, retaining its actual kernel. -/
theorem length_euler_of_exact (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hg : Function.Surjective g) (hex : Function.Exact f g) :
    Module.length R P + Module.length R M =
      Module.length R N + Module.length R (ker f) := by
  have h₁ := Module.length_eq_add_of_exact (ker f.rangeRestrict).subtype
    f.rangeRestrict (Submodule.subtype_injective _) f.surjective_rangeRestrict
    (exact_subtype_ker_map f.rangeRestrict)
  rw [ker_rangeRestrict] at h₁
  have h₂ := Module.length_eq_add_of_exact (range f).subtype g
    (Submodule.subtype_injective _) hg
    (show Function.Exact (range f).subtype g by
      rw [exact_iff, Submodule.range_subtype, exact_iff.mp hex])
  rw [h₁, h₂]
  ac_rfl

/-- A right exact pair with finite-length middle term is left injective if its
outer lengths already account for at most the middle length. -/
theorem injective_of_length_add_le (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hg : Function.Surjective g) (hex : Function.Exact f g)
    (hN : IsFiniteLength R N)
    (hlen : Module.length R P + Module.length R M ≤ Module.length R N) :
    Function.Injective f := by
  rw [length_euler_of_exact f g hg hex] at hlen
  have hk : Module.length R (ker f) = 0 := by
    apply le_antisymm _ zero_le
    apply (ENat.add_le_add_iff_left (Module.length_ne_top_iff.mpr hN)).mp
    simpa only [add_zero] using hlen
  have : Subsingleton (ker f) := Module.length_eq_zero_iff.mp hk
  intro x y hxy
  have hz : f (x - y) = 0 := by simp [map_sub, hxy]
  have he : (⟨x - y, hz⟩ : ker f) = 0 := Subsingleton.elim _ _
  exact sub_eq_zero.mp (congrArg Subtype.val he)

end LinearMap

namespace TensorProduct

variable {R : Type*} {C : Type*} {P : Type*} [CommRing R] [AddCommGroup C] [Module R C]
    [AddCommGroup P] [Module R P]

/-- Tensoring a finite based module multiplies length by its basis cardinality. -/
theorem length_of_basis {ι : Type*} [Fintype ι] (b : Module.Basis ι R P) :
    Module.length R (C ⊗[R] P) = Fintype.card ι * Module.length R C := by
  classical
  let e : C ⊗[R] P ≃ₗ[R] (ι → C) :=
    (TensorProduct.congr (LinearEquiv.refl R C) b.equivFun).trans
      (TensorProduct.piScalarRight R R C ι)
  rw [e.length_eq, Module.length_pi_of_fintype]
  simp

variable {P₁ : Type*} {M : Type*} [AddCommGroup P₁] [Module R P₁]
    [AddCommGroup M] [Module R M]

/-- The finite-length Euler obstruction for tensoring a finite-free presentation.
No injectivity of the original first map, locality, or Noetherian hypothesis is
needed. The rank relation is kept explicit. -/
theorem injective_lTensor_of_length_le {ι₁ : Type*} {ι₀ : Type*} [Fintype ι₁] [Fintype ι₀]
    (b₁ : Module.Basis ι₁ R P₁) (b₀ : Module.Basis ι₀ R P)
    (f : P₁ →ₗ[R] P) (g : P →ₗ[R] M)
    (hg : Function.Surjective g) (hex : Function.Exact f g)
    (hC : IsFiniteLength R C) (r : ℕ)
    (hr : Fintype.card ι₀ = Fintype.card ι₁ + r)
    (hlen : Module.length R (C ⊗[R] M) ≤ r * Module.length R C) :
    Function.Injective (f.lTensor C) := by
  apply LinearMap.injective_of_length_add_le (f.lTensor C) (g.lTensor C)
    (LinearMap.lTensor_surjective C hg) (_root_.lTensor_exact C hex hg)
  · apply Module.length_ne_top_iff.mp
    rw [length_of_basis b₀]
    exact WithTop.mul_ne_top (ENat.natCast_ne_top _) (Module.length_ne_top_iff.mpr hC)
  · rw [length_of_basis b₁, length_of_basis b₀, hr, Nat.cast_add, add_mul]
    simpa only [add_comm] using add_le_add_right hlen
      ((Fintype.card ι₁ : ℕ∞) * Module.length R C)

end TensorProduct
