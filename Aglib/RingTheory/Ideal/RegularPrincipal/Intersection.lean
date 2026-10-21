/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Aglib.RingTheory.Ideal.RegularPrincipal
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Regular principal ideals and intersection with a ring kernel

Every generator of an ideal linearly equivalent to the ring is regular.
If the image of a principal generator under a ring map is regular, product
with the actual ring kernel equals intersection with that kernel.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

universe u v

namespace Ideal

/-- Every generator of an ideal with an actual rank-one free presentation is regular.
The argument uses the existing regular-generator theorem and factor regularity. -/
theorem isSMulRegular_generator_of_linearEquiv {R : Type u} [CommRing R]
    (I : Ideal R) (e : I ≃ₗ[R] R) (a : R) (hI : I = span {a}) :
    IsSMulRegular R a := by
  obtain ⟨b, hb, hIb⟩ := ideal_exists_regular_generator I e
  have hbI : b ∈ I := hIb ▸ mem_span_singleton_self b
  obtain ⟨r, hr⟩ := mem_span_singleton'.mp (hI ▸ hbI)
  rw [← hr] at hb
  exact hb.of_smul r

/-- If a principal ideal's generator has regular image, its product with the actual
ring kernel equals its intersection with that kernel. Surjectivity of the ring map
and regularity of the generator in the original ring are unnecessary. -/
theorem mul_ker_eq_inf_of_regular_image {R : Type u} {S : Type v}
    [CommRing R] [CommRing S] (φ : R →+* S)
    (I : Ideal R) (a : R) (hI : I = span {a}) (ha : IsSMulRegular S (φ a)) :
    I * RingHom.ker φ = I ⊓ RingHom.ker φ := by
  apply le_antisymm mul_le_inf
  intro x hx
  obtain ⟨r, rfl⟩ := mem_span_singleton'.mp (hI ▸ hx.1)
  have hr : r ∈ RingHom.ker φ := by
    apply RingHom.mem_ker.mpr
    apply ha
    have hzero := RingHom.mem_ker.mp hx.2
    simpa only [map_mul, smul_eq_mul, mul_comm, mul_zero, zero_mul] using hzero
  exact mul_mem_mul_rev (hI ▸ mem_span_singleton_self a) hr

end Ideal
