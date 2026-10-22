/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Ideal.Operations

/-! # Ideal bounds on defects through original linear comparisons

A commuting square of linear equivalences transports the same ideal bound on
both kernel and cokernel. No finiteness, flatness or scalar extension is
assumed; the square must identify the actual original maps.
-/

@[expose] public section
namespace LinearMap

/-- Original linear equivalences preserve one common ideal bound on both defects. -/
theorem defectBounds_of_equiv
    {R U V P Q : Type*} [CommRing R]
    [AddCommGroup U] [Module R U] [AddCommGroup V] [Module R V]
    [AddCommGroup P] [Module R P] [AddCommGroup Q] [Module R Q]
    (f : U →ₗ[R] V) (g : P →ₗ[R] Q) (e : U ≃ₗ[R] P) (d : V ≃ₗ[R] Q)
    (h : ∀ x, g (e x) = d (f x)) (J : Ideal R)
    (hk : J • f.ker = ⊥) (hc : J • (⊤ : Submodule R V) ≤ f.range) :
    J • g.ker = ⊥ ∧ J • (⊤ : Submodule R Q) ≤ g.range := by
  constructor
  · apply le_antisymm _ bot_le
    apply Submodule.smul_le.mpr
    intro a ha x hx
    obtain ⟨y, rfl⟩ := e.surjective x
    have hy : y ∈ f.ker := by
      apply d.injective
      rw [LinearEquiv.map_zero]
      exact (h y).symm.trans hx
    have hz := Submodule.smul_mem_smul ha hy
    rw [hk] at hz
    change a • e y = 0
    rw [← LinearEquiv.map_smul, hz, LinearEquiv.map_zero]
  · apply Submodule.smul_le.mpr
    intro a ha x _
    obtain ⟨y, rfl⟩ := d.surjective x
    obtain ⟨z, hz⟩ := hc (Submodule.smul_mem_smul ha
      (Submodule.mem_top : y ∈ ⊤))
    refine ⟨e z, ?_⟩
    rw [h]
    exact (congrArg d hz).trans (LinearEquiv.map_smul d a y)


end LinearMap
