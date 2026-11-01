/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Ramification index of an actual uniformizer equation

The native ramification index is the exponent in the image of the original
uniformizer in a finite torsion-free extension of DVRs. This is independent of
any field-degree formula, pure degree, perfectness, or residue separability.
-/

@[expose] public noncomputable section

open IsLocalRing

namespace IsDiscreteValuationRing

variable (A B : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B]

/-- The native ramification index is the literal exponent in the image of
the original uniformizer. This comparison is derived, not an extra index premise. -/
theorem ramificationIdx_eq_uniformizerExponent
    {π : A} {τ : B} (hπ : Irreducible π) (hτ : Irreducible τ)
    (u : Bˣ) (e : ℕ) (he : algebraMap A B π = (u : B) * τ ^ e) :
    (maximalIdeal B).ramificationIdx A = e := by
  let : IsLocalHom (algebraMap A B) := inferInstance
  have hm : (maximalIdeal A).map (algebraMap A B) = maximalIdeal B ^ e := by
    rw [hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton, he,
      Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      ← hτ.maximalIdeal_eq]
  have hA : maximalIdeal A ≠ ⊥ := by
    rw [hπ.maximalIdeal_eq, ne_eq, Ideal.span_singleton_eq_bot]
    exact hπ.ne_zero
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal A) (maximalIdeal B) hA]
  apply Ideal.ramificationIdx'_spec
  · exact hm.le
  · rw [hm]
    intro hle
    have hvalue (n : ℕ) : idealOrderIsoENat B (maximalIdeal B ^ n) =
        OrderDual.toDual (n : ℕ∞) := by
      rw [← idealOrderIsoENat_symm_apply_coe B n]
      exact (idealOrderIsoENat B).apply_symm_apply (OrderDual.toDual (n : ℕ∞))
    have hbad := (idealOrderIsoENat B).monotone hle
    rw [hvalue, hvalue] at hbad
    change (e + 1 : ℕ∞) ≤ e at hbad
    have hnat : e + 1 ≤ e := by exact_mod_cast hbad
    exact (Nat.not_succ_le_self e) hnat

end IsDiscreteValuationRing
