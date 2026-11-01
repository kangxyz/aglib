/-
Copyright (c) 2026 Aglib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-! # The actual vanishing factor of a standard etale presentation

A factor is chosen inside the kernel of the original evaluation into a domain.
The original derivative-unit equation then makes its cofactor a unit. This is
an algebraic step towards an actual hypersurface open, not relative openness
or a geometric-integrality spreading statement.
-/

@[expose] public noncomputable section

namespace RingHom

/-- A nonzero element vanishing in a domain has an irreducible factor in the
kernel of the same homomorphism. No injectivity of that homomorphism is assumed. -/
theorem exists_irreducible_factor_map_eq_zero
    {R S : Type*} [CommRing R] [WfDvdMonoid R] [CommRing S] [IsDomain S]
    (φ : R →+* S) (a : R) (ha : a ≠ 0) (hφ : φ a = 0) :
    ∃ p q : R, Irreducible p ∧ a = p * q ∧ φ p = 0 := by
  revert ha hφ
  induction a using WfDvdMonoid.induction_on_irreducible with
  | zero => intro ha _; exact (ha rfl).elim
  | unit a hu => intro _ hφ; exact ((hu.map φ).ne_zero hφ).elim
  | mul a p ha hp ih =>
      intro _ hφ
      have hz : φ p = 0 ∨ φ a = 0 := mul_eq_zero.mp (by simpa only [map_mul] using hφ)
      rcases hz with hz | hz
      · exact ⟨p, a, hp, rfl, hz⟩
      · obtain ⟨q, r, hq, heq, hqz⟩ := ih ha hz
        refine ⟨q, p * r, hq, ?_, hqz⟩
        rw [heq]
        ac_rfl

end RingHom

namespace StandardEtalePair

open Polynomial

/-- In the original domain receiving a standard etale pair, one irreducible
factor vanishes and its cofactor is a unit. Both derivative and localization
unit statements refer to the same root and the same factorization. -/
theorem exists_irreducible_factor_hasMap
    {R S : Type*} [CommRing R] [IsDomain R] [WfDvdMonoid R[X]]
    [CommRing S] [IsDomain S] [Algebra R S]
    (P : StandardEtalePair R) (x : S) (h : P.HasMap x) :
    ∃ p q : R[X], Irreducible p ∧ P.f = p * q ∧ aeval x p = 0 ∧
      IsUnit (aeval x q) ∧ IsUnit (aeval x p.derivative) ∧
      IsUnit (aeval x (P.g * q)) := by
  obtain ⟨p, q, hp, hf, hx⟩ :=
    RingHom.exists_irreducible_factor_map_eq_zero (aeval x).toRingHom P.f
      P.monic_f.ne_zero h.1
  change aeval x p = 0 at hx
  have hd : IsUnit (aeval x p.derivative * aeval x q) := by
    have hd := h.isUnit_derivative_f
    rw [hf, derivative_mul, map_add, map_mul, map_mul, hx, zero_mul, add_zero] at hd
    exact hd
  have hq := isUnit_of_mul_isUnit_right hd
  refine ⟨p, q, hp, hf, hx, hq, isUnit_of_mul_isUnit_left hd, ?_⟩
  rw [map_mul]
  exact h.2.mul hq

end StandardEtalePair
