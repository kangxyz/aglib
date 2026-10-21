/-
Copyright (c) 2026 kangxyz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kangxyz
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Recovering equations from selected relations at sufficient precision

A nonzero polynomial value remains nonzero at sufficiently close points of an
adically separated ring. This allows a common multiplier to be cancelled in a
domain after evaluation, without assuming it is a unit. Injectivity then recovers
the original equations in the source ring, which need not itself be assumed a domain.
-/

@[expose] public section

namespace MvPolynomial

variable {A B C σ ι κ : Type*} [CommRing A] [CommRing B] [CommRing C]

/-- A polynomial nonzero at a point stays nonzero at sufficiently close points
in an adically separated ring, with any prescribed lower bound on precision. -/
theorem exists_precision_eval₂_ne_zero (I : Ideal C) [IsHausdorff I C]
    (f : A →+* C) (h : MvPolynomial σ A) (y : σ → C)
    (hy : eval₂ f y h ≠ 0) (c : ℕ) :
    ∃ N : ℕ, c ≤ N ∧ ∀ z : σ → C,
      (∀ j, z j - y j ∈ I ^ N) → eval₂ f z h ≠ 0 := by
  have hn : ∃ n : ℕ, eval₂ f y h ∉ I ^ n := by
    by_contra! hall
    apply hy
    apply IsHausdorff.haus (inferInstance : IsHausdorff I C)
    intro n
    simpa only [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top] using hall n
  obtain ⟨n, hn⟩ := hn
  refine ⟨max c n, le_max_left _ _, ?_⟩
  intro z hz hz0
  have hcoords : (fun j => Ideal.Quotient.mk (I ^ n) (z j)) =
      fun j => Ideal.Quotient.mk (I ^ n) (y j) := by
    funext j
    apply Ideal.Quotient.eq.mpr
    exact (Ideal.pow_le_pow_right (le_max_right c n)) (hz j)
  have heval : Ideal.Quotient.mk (I ^ n) (eval₂ f z h) =
      Ideal.Quotient.mk (I ^ n) (eval₂ f y h) := by
    rw [hom_eval₂, hom_eval₂, hcoords]
  apply hn
  apply (Ideal.Quotient.eq_zero_iff_mem).mp
  rw [← heval, hz0, map_zero]

/-- Selected relations recover all original source equations at sufficient
precision when a common multiplier is nonzero at the formal point. Cancellation
occurs only in the target domain, then injectivity returns the source equations. -/
theorem exists_precision_recover_equations (I : Ideal C) [IsHausdorff I C]
    [IsDomain C] (φ : A →+* B) (τ : B →+* C) (hτ : Function.Injective τ)
    (G : κ → MvPolynomial σ A) (F : ι → MvPolynomial σ A)
    (h : MvPolynomial σ A) (hmem : ∀ i, h * F i ∈ Ideal.span (Set.range G))
    (y : σ → C) (hy : eval₂ (τ.comp φ) y h ≠ 0) (c : ℕ) :
    ∃ N : ℕ, c ≤ N ∧ ∀ x : σ → B,
      (∀ j, τ (x j) - y j ∈ I ^ N) →
      (∀ j, eval₂ φ x (G j) = 0) → ∀ i, eval₂ φ x (F i) = 0 := by
  obtain ⟨N, hc, hN⟩ := exists_precision_eval₂_ne_zero I (τ.comp φ) h y hy c
  refine ⟨N, hc, ?_⟩
  intro x hx hG i
  have hker : Ideal.span (Set.range G) ≤ RingHom.ker (eval₂Hom φ x) := by
    apply Ideal.span_le.mpr
    rintro q ⟨j, rfl⟩
    exact RingHom.mem_ker.mpr (hG j)
  have hprod : eval₂ φ x h * eval₂ φ x (F i) = 0 := by
    have hh := RingHom.mem_ker.mp (hker (hmem i))
    rw [map_mul] at hh
    change eval₂ φ x h * eval₂ φ x (F i) = 0 at hh
    exact hh
  have hnonzero : τ (eval₂ φ x h) ≠ 0 := by
    rw [hom_eval₂]
    exact hN (fun j => τ (x j)) hx
  apply hτ
  rw [map_zero]
  have htarget : τ (eval₂ φ x h) * τ (eval₂ φ x (F i)) = 0 := by
    simpa only [map_mul, map_zero] using congrArg τ hprod
  exact (mul_eq_zero.mp htarget).resolve_left hnonzero

end MvPolynomial
