/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-!
# Extensions preserving a uniformizer

A homomorphism of discrete valuation rings sending a uniformizer to a
uniformizer is injective and local, and extension of ideals preserves the
native extended-natural order, including the infinite order of the zero ideal.
-/

@[expose] public section

namespace IsDiscreteValuationRing

open IsLocalRing

universe u v

variable {R : Type u} {S : Type v} [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R] [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
  (ψ : R →+* S) {p : R} (hp : Irreducible p) (hψp : Irreducible (ψ p))

include hp hψp

/-- A map preserving a uniformizer is injective. -/
theorem injective_of_map_irreducible : Function.Injective ψ := by
  apply (injective_iff_map_eq_zero ψ).mpr
  intro x hx
  by_contra hne
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hne hp
  rw [map_mul, map_pow] at hx
  exact (mul_ne_zero (u.isUnit.map ψ).ne_zero (pow_ne_zero n hψp.ne_zero)) hx

/-- The actual maximal ideal extends to the target maximal ideal. -/
theorem map_maximalIdeal_of_map_irreducible :
    (maximalIdeal R).map ψ = maximalIdeal S := by
  rw [hp.maximalIdeal_eq, hψp.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]

/-- A map preserving a uniformizer is a local ring homomorphism. -/
theorem isLocalHom_of_map_irreducible : IsLocalHom ψ := by
  refine ⟨fun x hx => ?_⟩
  by_contra h
  have hxmem : x ∈ maximalIdeal R := h
  have hy := Ideal.mem_map_of_mem ψ hxmem
  rw [map_maximalIdeal_of_map_irreducible ψ hp hψp] at hy
  exact hy hx

/-- Extension of every ideal preserves the native DVR order. In particular,
this includes the zero ideal, whose order is infinity. -/
theorem idealOrderIsoENat_map_of_map_irreducible (I : Ideal R) :
    idealOrderIsoENat S (I.map ψ) = idealOrderIsoENat R I := by
  by_cases hI : I = ⊥
  · simp [hI]
  obtain ⟨n, rfl⟩ := ideal_eq_span_pow_irreducible hI hp
  rw [Ideal.map_span, Set.image_singleton, map_pow,
    ← idealOrderIsoENat_symm_apply_coe_of_irreducible n hψp,
    ← idealOrderIsoENat_symm_apply_coe_of_irreducible n hp]
  simp only [OrderIso.apply_symm_apply]

end IsDiscreteValuationRing
