/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.Flat.Basic

/-!
# Tensoring an injection with a finite module's dual

A finite module's dual embeds in a finite free module by dualizing a finite
free surjection. Native tensor-map injectivity then shows that an injection
with flat source remains injective after tensoring with this dual. The target
of the original injection need not be flat. All carrier universes are independent.
-/

@[expose] public section

namespace LinearMap

variable {R : Type*} [CommRing R]
    {M : Type*} [AddCommGroup M] [Module R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    (L : Type*) [AddCommGroup L] [Module R L] [Module.Finite R L]

/-- Tensoring an injection from a flat module with the dual of a finite module
preserves injectivity, without requiring a flat target. -/
theorem rTensor_dual_injective_of_flat [Module.Flat R M]
    (f : M →ₗ[R] N) (hf : Function.Injective f) :
    Function.Injective (f.rTensor (Module.Dual R L)) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' R L
  have hmap := TensorProduct.map_injective_of_flat_flat' f p.dualMap hf
    (LinearMap.dualMap_injective_of_surjective hp)
  rw [← LinearMap.lTensor_comp_rTensor] at hmap
  intro x y hxy
  apply hmap
  exact congrArg (p.dualMap.lTensor N) hxy

end LinearMap
